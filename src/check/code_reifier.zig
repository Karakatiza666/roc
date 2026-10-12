//! Reification: a checked function body becomes a `Code.Ir` value in the
//! module's `ConstStore`.
//!
//! The output is a tree of `ConstValue` nodes shaped like the `Ir`, `Ty` and
//! `Lit` tag unions declared in `Builtin.roc`'s `Code` block. Those three are
//! transparent nominals (`:=`), so the reifier emits bare tags and the restore
//! path unwraps the nominal wrapper on the way back out.
//!
//! A site holds `Code`'s backing, `{ defs, root }`. A call names its callee
//! and the walk descends into it, so the structure the author wrote survives
//! into the target and the table holds one description per definition the
//! calls reach.
//!
//! A construct the `Ir` cannot describe stops the walk and names itself, so the
//! diagnostic points at the expression the user wrote rather than at a type.

const std = @import("std");
const base = @import("base");
const collections = @import("collections");

const CIR = @import("can").CIR;
const ModuleEnv = @import("can").ModuleEnv;
const canonical = @import("canonical_names.zig");
const checked = @import("checked_artifact.zig");
const const_store = @import("const_store.zig");
const static_dispatch = @import("static_dispatch_registry.zig");
const numeral = @import("types").numeral;

const Allocator = std.mem.Allocator;

const ConstNodeId = const_store.ConstNodeId;
const ConstBlobDataId = const_store.ConstBlobDataId;
const ConstStore = const_store.ConstStore;
const CheckedExprId = checked.CheckedExprId;
const CheckedPatternId = checked.CheckedPatternId;
const CheckedStatementId = checked.CheckedStatementId;
const CheckedTypeId = checked.CheckedTypeId;

/// Why a function could not be described as a `Code.Ir`.
pub const Rejection = struct {
    kind: Kind,
    region: base.Region,
    /// Names the offending construct, binding or type. Borrowed from a name
    /// store or a static string; valid as long as the artifact is.
    detail: []const u8,

    pub const Kind = enum {
        /// An expression form outside the `Ir` (`detail` names the form).
        unsupported_expression,
        /// A type outside the `Ty` (`detail` names the type constructor).
        unsupported_type,
        /// A type variable that checking left open.
        unresolved_type,
        /// A binding from outside the staged function.
        capture,
        /// An effectful function, `dbg`, or a hosted lambda.
        effect,
        /// A reference the compiler cannot follow to a definition.
        unresolved_reference,
        /// A template argument the compiler cannot fix while it runs. The
        /// region is the argument, which is all this one has to say.
        argument_not_constant,
    };
};

/// The operator methods the `Ir` carries as `Binop` or `Unary` rather than as
/// a `Call`, resolved to ids once so the walk compares ids and never text.
const OperatorNames = struct {
    binop: [binop_texts.len]?canonical.MethodNameId,
    negate: ?canonical.MethodNameId,
    not: ?canonical.MethodNameId,
    range_exclusive: ?canonical.MethodNameId,
    range_inclusive: ?canonical.MethodNameId,

    /// Every operator in Roc desugars to one of these methods.
    const binop_texts = [_][]const u8{
        "plus",  "minus",  "times", "div_by", "div_trunc_by", "rem_by",
        "is_lt", "is_lte", "is_gt", "is_gte", "is_eq",
    };

    fn resolve(names: *const canonical.CanonicalNameStore) OperatorNames {
        var binop: [binop_texts.len]?canonical.MethodNameId = undefined;
        for (binop_texts, 0..) |text, index| binop[index] = names.lookupMethodName(text);
        return .{
            .binop = binop,
            .negate = names.lookupMethodName("negate"),
            .not = names.lookupMethodName("not"),
            .range_exclusive = names.lookupMethodName("range_exclusive_to"),
            .range_inclusive = names.lookupMethodName("range_inclusive_to"),
        };
    }

    fn isBinop(self: OperatorNames, method: canonical.MethodNameId) bool {
        for (self.binop) |candidate| {
            if (candidate) |id| {
                if (id == method) return true;
            }
        }
        return false;
    }

    /// Which end a range reaches, or null where the method builds no range.
    ///
    /// `a..<b` reaches the walk as a call to one of these rather than as the
    /// operator it was written as, because that is what the checker resolves
    /// it to.
    fn rangeEnd(self: OperatorNames, method: canonical.MethodNameId) ?[]const u8 {
        if (self.range_exclusive) |id| {
            if (id == method) return "Exclusive";
        }
        if (self.range_inclusive) |id| {
            if (id == method) return "Inclusive";
        }
        return null;
    }

    /// The `Unary` operator name for a method, or null when it is neither.
    fn unaryOp(self: OperatorNames, method: canonical.MethodNameId) ?[]const u8 {
        if (self.negate) |id| {
            if (id == method) return "neg";
        }
        if (self.not) |id| {
            if (id == method) return "not";
        }
        return null;
    }
};

/// Bool's two tags, resolved once so the walk compares ids rather than text.
///
/// A written `Bool.True` reaches the walk as a bare tag under the `Bool`
/// nominal, and only the tag's name says which of the two it is.
const BoolTags = struct {
    true_tag: ?canonical.TagLabelId,
    false_tag: ?canonical.TagLabelId,

    fn resolve(names: *const canonical.CanonicalNameStore) BoolTags {
        return .{
            .true_tag = names.lookupTagLabel("True"),
            .false_tag = names.lookupTagLabel("False"),
        };
    }

    /// Which of the two a tag label is, or null when it is neither.
    fn value(self: BoolTags, label: canonical.TagLabelId) ?bool {
        if (self.true_tag) |id| {
            if (id == label) return true;
        }
        if (self.false_tag) |id| {
            if (id == label) return false;
        }
        return null;
    }
};

/// The builtin that joins two strings, under the export name every builtin
/// call carries. A written `a.concat(b)` and a join an interpolated literal
/// implies therefore reach a translator as one name.
const str_concat_name = "Builtin.Str.concat";

/// The builtin definitions the `Ir` carries as an operator node rather than as
/// a `Call`, resolved to ids once so the walk compares ids and never text.
///
/// A written `!b`, `Bool.not(b)` and `b.not()` are the one operation, so the
/// first two describe as the `Unary` the third already describes as.
const BuiltinOperators = struct {
    not: ?canonical.ExportNameId,

    /// Builtin names a definition by the path that reaches it, so the whole
    /// path is the key.
    fn resolve(names: *const canonical.CanonicalNameStore) BuiltinOperators {
        return .{ .not = names.lookupExportName("Builtin.Bool.not") };
    }

    /// The `Unary` operator name a builtin definition is, or null when it is
    /// none of them.
    fn unaryOp(self: BuiltinOperators, export_name: canonical.ExportNameId) ?[]const u8 {
        if (self.not) |id| {
            if (id == export_name) return "not";
        }
        return null;
    }
};

/// A definition the walk reaches, named by the module that defines it and the
/// checked body it is.
///
/// A checked id belongs to one module, so the module is half the key. The
/// module is its artifact's identity rather than the whole key, which is 32
/// bytes instead of six hashes.
pub const DefinitionKey = struct {
    artifact: [32]u8,
    body: CheckedExprId,
    /// Which instantiation of a generic definition this row is, digested from
    /// the types its quantified variables were fixed to. Zero for a definition
    /// that has none, so one body describes once.
    instantiation: [32]u8 = @as([32]u8, @splat(0)),
    /// Whether this row flattens a curried definition: parameters are the
    /// outer lambda's followed by the inner's, and the body is the inner body.
    /// A definition constructed at one site and run at another takes one row
    /// of each shape.
    curried: bool = false,
    /// Whether this row reads the block around it by replaying the statements
    /// it reads at the head of its body, rather than by taking what it
    /// captured as leading parameters. One lambda can be described each way:
    /// at a `Code` position or as a template's argument, and as a call.
    replayed: bool = false,
    /// Which definitions this row's function parameters were fixed to,
    /// digested from the rows they name. Zero for a definition that takes no
    /// function parameter, so one body describes once.
    callees: [32]u8 = @as([32]u8, @splat(0)),
};

/// A definition some description's `Call` names.
///
/// `node` is null while the walk is inside the definition, which is what makes
/// a recursive call terminate: the call names the definition and the walk does
/// not enter it a second time.
const Definition = struct {
    /// Module-qualified, and owned here. Null only for a site's own root until
    /// a call reaches it, because nothing else names the root.
    name: ?[]u8,
    node: ?ConstNodeId,
    /// What this definition calls, in the order the walk met them.
    callees: []DefinitionKey,
};

/// Either the description a site holds or the first construct that stopped the
/// walk.
///
/// The description is `Code`'s backing, `{ defs, root }`: the body the site
/// named, and one row per definition its calls reach.
pub const Outcome = union(enum) {
    reified: ConstNodeId,
    rejected: Rejection,
};

/// Reads a checked module and writes `Code.Ir` nodes into its const store.
pub const Reifier = struct {
    gpa: Allocator,
    store: *ConstStore,
    types: checked.CheckedTypeStoreView,
    bodies: checked.CheckedBodyStoreView,
    plans: *const static_dispatch.StaticDispatchPlanTable,
    names: *const canonical.CanonicalNameStore,
    artifact: checked.CheckedModuleArtifactKey,
    value_refs: *const checked.ResolvedValueRefTable,
    procedure_bindings: *const checked.TopLevelProcedureBindingTable,
    procedure_templates: *const checked.CheckedProcedureTemplateTable,
    const_templates: *const checked.ConstTemplateTable,
    const_bodies: *const checked.CheckedConstBodyTable,
    env: *const ModuleEnv,
    operators: OperatorNames,
    bool_tags: BoolTags,
    /// Binders visible inside the staged function, innermost last. A lookup
    /// that misses this scope is a capture.
    scope: std.ArrayList(Binding) = .empty,
    /// What a root written at its site reads from the block around it, while
    /// that root is walked. Null everywhere else, a lifted row among them:
    /// a row takes what it captured as parameters.
    replay: ?*Replay = null,
    /// Memoizes `Ty` nodes so a type repeated across a body costs one subtree.
    type_cache: collections.DenseMapUnmanaged(CheckedTypeId, ConstNodeId) = .empty,
    /// The types `tyNode` is part way through building. Roc reaches recursion
    /// only through a nominal, and `nominal_in_progress` closes that, so a type
    /// that reaches itself any other way has no description and is refused
    /// rather than recursed into forever.
    ///
    /// Keyed by the enclosing instantiation as well as the id, because a
    /// declaration's backing is one template every use shares: `Chain(F32)`
    /// and the `Chain(U16)` written inside it walk the same backing id under
    /// different bindings, and the second is not the first reaching itself.
    type_in_progress: std.AutoHashMapUnmanaged(TypeFrame, void) = .empty,
    /// Nominals that a `Ty.Recursive` written so far still refers to. A
    /// `Named` closes its own, and a subtree left holding one names a nominal
    /// it does not contain, so what that subtree means depends on where it
    /// sits rather than on its type id alone.
    open_recursions: collections.DenseMapUnmanaged(CheckedTypeId, void) = .empty,
    /// The nominals `nominalTyNode` is part way through building, each keyed by
    /// the declaration and what this use fixed its variables to, and each
    /// valued by the checked id the `Named` being built carries.
    ///
    /// A nominal reaches itself through its declaration's backing, which is one
    /// template every use shares, so `Tree(U16)` and the `Tree(a)` written
    /// inside it are one type under two ids. What the two have in common is the
    /// nominal and the arguments, which is what this is keyed by.
    nominal_in_progress: std.AutoHashMapUnmanaged([32]u8, CheckedTypeId) = .empty,
    /// The innermost nominal instantiation `tyNode` is walking inside, zero
    /// where the walk is inside none.
    nominal_instance: [32]u8 = @splat(0),
    /// Where every node of a folded constant says it was written, while the
    /// walk is inside one. The value was written at the definition, possibly
    /// in another module, and the author reading a translator's report is
    /// looking at the body in front of them, so the name's place is the useful
    /// one. Resolved by the reader that saw the name, because a region means
    /// nothing to the module that did not.
    folded_origin: ?FoldedOrigin = null,
    /// The constants the walk is part way through folding. A definition that
    /// reads itself is refused on the repeat rather than followed forever.
    folding: collections.DenseMapUnmanaged(CheckedExprId, void) = .empty,
    /// Names the walk invented for binders no author wrote. Owned here,
    /// because a `Binding` and the `Str` beside it both read one and the walk
    /// outlives the call that made it.
    invented_names: std.ArrayList([]u8) = .empty,
    /// How many versions of each `var` this row has bound. A count of the
    /// versions in scope would restart where a branch popped one, and the
    /// two would go by the same name in a row that binds both.
    var_versions: collections.DenseMapUnmanaged(checked.PatternBinderId, u32) = .empty,
    /// The loop the walk is inside, innermost first entry, or null outside
    /// one. A `break` reads it for the state it settles, and a `return` reads
    /// it to know that the transfer has to be said rather than rewritten.
    loop: ?Loop = null,
    /// The constructs lifted out of the expression being described, each
    /// paired with the node the branch being described gives it. Several,
    /// because `Ok(a? + b?)` lifts one per `?`.
    lifts: std.ArrayList(Lift) = .empty,
    /// Serial for the binder names a derived tag union comparison generates,
    /// so two of them never write the same name.
    derived_binder_serial: u32 = 0,
    /// What the quantified variables of the definition being walked stand for.
    /// Empty while the walk is inside one that has none, which is every
    /// definition a monomorphic program writes.
    ///
    /// Borrowed from the call that fixed them, and restored on the way out, so
    /// one reader walks the same body once per instantiation.
    substitution: Substitution = .empty,
    /// How often `substitution` has answered, so a `Ty` subtree can tell
    /// whether it means anything beyond its own type id.
    substitution_uses: u32 = 0,
    /// How the call that fixed this definition's quantified variables
    /// discharged its `where` obligations, in canonical evidence-param order.
    /// Empty while the walk is inside a definition with none.
    ///
    /// A constrained body names its own evidence param rather than a target,
    /// so `value.encoder_for` reads the same whether the compiler derived it
    /// or the author wrote it. The call knows which, and the walk already
    /// enters the body once per instantiation.
    evidence: SuppliedEvidence = .{},
    /// Which definition each function parameter of this row was fixed to, by
    /// the call that wrote the row. Empty while the walk is inside a
    /// definition that takes no function parameter.
    ///
    /// The `Ir` is first order, so a function value is resolved at the site
    /// that fixes it, the way a quantified variable is. Owned by that call.
    bound: []const BoundCallee = &.{},
    /// The lambda whose parameters `bound` numbers, so a lambda nested inside
    /// that row binds its own parameters as parameters.
    bound_lambda: ?CheckedExprId = null,
    /// What each parametric nominal in the type being walked fixed its
    /// declared variables to, innermost last. Owned here, because a nominal
    /// binds for the span of its own backing rather than of a definition.
    nominal_args: Substitution = .empty,
    /// What this reader shares with every other module's reader: the table
    /// being built, who calls whom, the strings already written, and the first
    /// refusal.
    walk: *Walk,

    /// The place a folded constant's nodes report, already resolved against
    /// the source of the module the name was written in.
    const FoldedOrigin = struct {
        module: []const u8,
        info: base.RegionInfo,
    };

    /// A checked type named where it lives.
    ///
    /// A type id is that module's, so a variable a call fixes carries the
    /// reader that can read what it was fixed to.
    const TypeRef = struct {
        reader: *Reifier,
        id: CheckedTypeId,
    };

    /// What each quantified variable of one definition stands for.
    const Substitution = collections.DenseMapUnmanaged(CheckedTypeId, TypeRef);

    /// One field of a record type, beside the reader its ids are canonical in.
    ///
    /// A record whose row a site fixed holds the fields the definition named
    /// in the definition's module and the rest in the site's, so a field's
    /// type and label mean something only beside the reader they came from.
    const FieldRef = struct {
        reader: *Reifier,
        field: checked.CheckedRecordField,
    };

    /// One type id, under the nominal instantiation the walk reached it in.
    const TypeFrame = struct {
        instance: [32]u8,
        id: CheckedTypeId,
    };

    /// One instantiation of a generic callee.
    ///
    /// `key` digests the types the variables were fixed to, in the scheme's
    /// own order, so two calls at one type share a row and two at different
    /// types take one each.
    const Instantiation = struct {
        substitution: Substitution,
        key: [32]u8,
    };

    /// What a refusal calls the use whose type was left open, so a call and a
    /// site each name themselves.
    ///
    /// `missing` is a use that carries no type at all, and `partial` a use
    /// that carries one naming fewer variables than the definition quantifies
    /// over. Each reads as the tail of the report's lead-in, "What is left
    /// open (not fixed):", which is where the plain wording and the technical
    /// one sit together so that no detail has to repeat the pair.
    const Unfixed = struct {
        missing: []const u8,
        partial: []const u8,

        const call = Unfixed{
            .missing = "the type this call gives its callee",
            .partial = "a type variable this call does not fix",
        };
        const site = Unfixed{
            .missing = "the type of this Code position",
            .partial = "a type variable at this Code position",
        };
    };

    /// What the description calls one definition by.
    ///
    /// A plain call reads the name off the binder its callee names, in the
    /// module that defines it. A method call has no binder at the site, and
    /// the `Call` spells it `Owner.method`, so the site hands that spelling
    /// over and the row answers to the same string.
    const CalleeSpelling = union(enum) {
        binder: checked.PatternBinderId,
        written: []const u8,
    };

    /// What one call supplied for its callee's `where` obligations, in
    /// canonical evidence-param order.
    ///
    /// `reader` is the module the call was written in, and both halves need
    /// it: an evidence node id indexes that module's plan table, and the types
    /// recorded beside it are named in that module's store. Null with no
    /// entries, which is a definition whose caller had no obligation to
    /// discharge.
    const SuppliedEvidence = struct {
        reader: ?*Reifier = null,
        entries: []const static_dispatch.CheckedEvidence = &.{},
    };

    /// The definition a call's callee names: which one, what names it, and the
    /// reader of the module that defines it.
    const CalleeTarget = struct {
        key: DefinitionKey,
        spelling: CalleeSpelling,
        reader: *Reifier,
        /// What this call fixes the callee's quantified variables to, or null
        /// when the callee has none. Owned by the call, and borrowed by the
        /// walk of the callee's body.
        instantiation: ?Instantiation = null,
        /// What this call supplies for the callee's `where` obligations.
        evidence: SuppliedEvidence = .{},
        /// Whether this row is a lambda lifted out of a block, which needs a
        /// serial because two functions can each write one of the same name.
        lifted: bool = false,
        /// What a lifted lambda captured, which its row takes as leading
        /// parameters and every call site passes first. Empty for every other
        /// callee.
        captures: []const checked.CheckedCapture = &.{},
        /// Which definition this call fixed each function parameter of the
        /// callee to. Owned by the call, and borrowed by the walk of the
        /// callee's body.
        bound: []BoundCallee = &.{},
        /// The function type a row that replays the block around it describes
        /// at. Null for every other row, which reads its own node's type.
        at: ?CheckedTypeId = null,
    };

    /// What one template argument fixes its parameter to: a value written
    /// into the description, or the definition a function argument names.
    pub const TemplateArg = union(enum) {
        value: ConstNodeId,
        callee: CalleeTarget,
    };

    /// One function parameter of a callee, fixed to the definition the call
    /// passed for it.
    const BoundCallee = struct {
        /// Which parameter this fixed, in the callee's own order.
        param: u32,
        target: CalleeTarget,
    };

    /// What a plain call's callee is: a definition the walk describes into the
    /// table, a function the compiler provides that the description only
    /// names, or an operator the `Ir` carries as a node of its own.
    const Callee = union(enum) {
        definition: CalleeTarget,
        provided: []const u8,
        unary: []const u8,
    };

    const Binding = struct {
        binder: checked.PatternBinderId,
        name: []const u8,
        kind: Kind,

        /// What a name in the staged scope stands for. A `constant` is a value
        /// a template call fixed, already described as a `Lit`, so a reference
        /// to it is that literal rather than a name the stage has to bind.
        ///
        /// A `function` is a function the block bound: a lambda written there,
        /// or one a call handed back. The `Ir` is first order, so neither
        /// leaves a `Let` behind; the payload is the expression that produced
        /// it, and the call that runs it is what describes it.
        const Kind = union(enum) {
            param,
            local,
            constant: ConstNodeId,
            function: CheckedExprId,
            /// A function parameter the call fixed to a definition, held as an
            /// index into the walk's bound callees. The `Ir` is first order,
            /// so a call on the parameter names that definition and the
            /// parameter itself is not in the row's signature.
            callee: u32,
        };
    };

    /// The statements of the block around a root that the root reads.
    ///
    /// A description carries no scope, so a value the root captures is bound
    /// at the head of the root's body by the statement that produced it, and
    /// a translator meets it as a local. A pure expression computes the same
    /// value on every call, so replaying it there describes what the body
    /// reads.
    const Replay = struct {
        /// The root, whose body the replayed statements wrap.
        root: CheckedExprId,
        /// The root's region, which no replayed statement sits inside: a
        /// statement there is one the root's own walk binds.
        region: base.Region,
        /// Each binder the root read from around it, under the binding a read
        /// resolves to until the statement binding it is replayed.
        bindings: collections.DenseMapUnmanaged(checked.PatternBinderId, Binding) = .empty,
        /// The statements still to wrap the body in.
        pending: std.ArrayList(CheckedStatementId) = .empty,

        fn deinit(self: *Replay, gpa: Allocator) void {
            self.bindings.deinit(gpa);
            self.pending.deinit(gpa);
        }
    };

    /// The parameters and body a lambda expression carries.
    const LambdaData = @FieldType(checked.CheckedExprData, "lambda");

    /// The type a nominal hands down to the expression building its backing.
    ///
    /// Both halves are needed: `node` is the `Ty` the description carries, and
    /// `checked` is what an arm asks about. `Bool.True` is a bare tag under
    /// the `Bool` nominal, so only the nominal's own checked type says the tag
    /// is a Bool rather than a variant of some union.
    const TypeOverride = struct {
        node: ConstNodeId,
        checked: CheckedTypeId,
    };

    /// `error.Rejected` unwinds the walk; the reason is in `self.rejection`.
    /// The loop the walk is inside: the `var`s its turn carries, and the type
    /// that state has. A `break` needs both, because it hands the state back.
    const Loop = struct {
        joins: []const Join,
        carried: ConstNodeId,
    };

    /// One construct lifted out of the expression that held it, and what the
    /// branch being described puts in its place.
    const Lift = struct {
        expr: CheckedExprId,
        node: ConstNodeId,
    };

    const Error = Allocator.Error || error{Rejected};

    /// The checked stores the walk reads. Publication runs the walk before it
    /// assembles the artifact, so the pieces are named rather than taken from
    /// one.
    ///
    /// Views rather than stores, because a walk into an imported module reads
    /// that module's published view and there is no store to read instead.
    pub const Sources = struct {
        types: checked.CheckedTypeStoreView,
        bodies: checked.CheckedBodyStoreView,
        plans: *const static_dispatch.StaticDispatchPlanTable,
        names: *const canonical.CanonicalNameStore,
        /// The module the walk reads, so a callee that resolves to a
        /// definition of another module is recognised as one.
        artifact: checked.CheckedModuleArtifactKey,
        /// What each checked lookup resolves to. A plain call reaches its
        /// callee's body through this rather than through the canonical
        /// module, because a module's source-node map is build-only and a
        /// deserialized module has none.
        value_refs: *const checked.ResolvedValueRefTable,
        procedure_bindings: *const checked.TopLevelProcedureBindingTable,
        procedure_templates: *const checked.CheckedProcedureTemplateTable,
        /// Where a name bound to a compile-time value leads. A constant the
        /// compiler fixed is folded into the description where the name
        /// stands, so the walk needs the template that holds its body.
        const_templates: *const checked.ConstTemplateTable,
        const_bodies: *const checked.CheckedConstBodyTable,
    };

    pub fn init(
        walk: *Walk,
        sources: Sources,
        env: *const ModuleEnv,
    ) Reifier {
        return .{
            .gpa = walk.gpa,
            .store = walk.store,
            .walk = walk,
            .types = sources.types,
            .bodies = sources.bodies,
            .plans = sources.plans,
            .names = sources.names,
            .artifact = sources.artifact,
            .value_refs = sources.value_refs,
            .procedure_bindings = sources.procedure_bindings,
            .procedure_templates = sources.procedure_templates,
            .const_templates = sources.const_templates,
            .const_bodies = sources.const_bodies,
            .env = env,
            .operators = OperatorNames.resolve(sources.names),
            .bool_tags = BoolTags.resolve(sources.names),
        };
    }

    /// The sources a finished artifact publishes, for a reader that already
    /// has one.
    pub fn artifactSources(artifact: *const checked.CheckedModuleArtifact) Sources {
        return .{
            .types = artifact.checked_types.view(),
            .bodies = artifact.checked_bodies.view(),
            .plans = &artifact.static_dispatch_plans,
            .names = &artifact.canonical_names,
            .artifact = artifact.key,
            .value_refs = &artifact.resolved_value_refs,
            .procedure_bindings = &artifact.top_level_procedure_bindings,
            .procedure_templates = &artifact.checked_procedure_templates,
            .const_templates = &artifact.const_templates,
            .const_bodies = &artifact.checked_const_bodies,
        };
    }

    pub fn deinit(self: *Reifier) void {
        self.scope.deinit(self.gpa);
        self.var_versions.deinit(self.gpa);
        self.lifts.deinit(self.gpa);
        self.type_cache.deinit(self.gpa);
        self.type_in_progress.deinit(self.gpa);
        self.open_recursions.deinit(self.gpa);
        self.nominal_in_progress.deinit(self.gpa);
        self.nominal_args.deinit(self.gpa);
        self.folding.deinit(self.gpa);
        for (self.invented_names.items) |name| self.gpa.free(name);
        self.invented_names.deinit(self.gpa);
    }

    /// Describe the lambda at `root` as a `Code`: the body, and every
    /// definition it calls.
    ///
    /// `root` is a lambda of the module being walked, so a call can reach it
    /// and the table has to be able to hold it. `site` is what the site fixed
    /// the root to: its template, the reader of the module the site was
    /// written in, and the `f` of the surrounding `Code(f)`.
    pub fn reifyLambda(self: *Reifier, root: CheckedExprId, site: Site) Allocator.Error!Outcome {
        return self.outcomeOf(self.rootSiteNode(root, site));
    }

    /// What a `Code(f)` position hands the root it stands at.
    pub const Site = struct {
        /// What the root quantifies over: its definition's template, or the
        /// scheme a block generalized its lambda to. Null for a lambda written
        /// at the site: it is checked against `f` directly, so it quantifies
        /// over nothing and there is nothing for `f` to fix.
        scheme: ?Scheme,
        /// Whether a block holds the root, so the root reads the block around
        /// it and describes at `fixed` rather than at a type of its own.
        in_block: bool,
        /// The reader of the module holding the site, which is the module
        /// `fixed` names its type in.
        caller: *Reifier,
        /// The `f` of the surrounding `Code(f)`. With a scheme it is what the
        /// site fixes the root's quantified variables to; a root in a block
        /// takes it as its own function type too, which a lambda written at
        /// the site needs because its node holds the `Code`.
        fixed: ?CheckedTypeId,
        region: base.Region,
    };

    /// A quantified function type: the variables a use fixes, and the type
    /// that holds them.
    pub const Scheme = struct {
        vars: []const CheckedTypeId,
        root: CheckedTypeId,
    };

    pub fn templateScheme(self: *Reifier, template: checked.CheckedProcedureTemplate) Scheme {
        return .{ .vars = self.schemeVars(template), .root = template.checked_fn_root };
    }

    /// The scheme a block generalized the lambda at `expr_id` to, or null for
    /// one it did not generalize. Publication gives every generalized local
    /// function a dispatch scope of its own, and the scope holds its scheme.
    fn localScheme(self: *Reifier, expr_id: CheckedExprId) ?Scheme {
        for (self.procedure_templates.dispatch_scopes) |*scope| {
            if (scope.checked_expr != expr_id) continue;
            return .{ .vars = self.procedure_templates.scopeSchemeVars(scope), .root = scope.scheme_root };
        }
        return null;
    }

    fn rootSiteNode(self: *Reifier, root: CheckedExprId, site: Site) Error!ConstNodeId {
        // The root is a use of its own definition, so the site fixes its
        // quantified variables the way a call fixes a callee's. The walk of
        // the root's body borrows the substitution and finishes here.
        var instance = if (site.scheme) |scheme|
            try self.instantiationOf(scheme, site.caller, site.fixed, site.region, .site)
        else
            null;
        defer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        const key = DefinitionKey{
            .artifact = self.artifact.bytes,
            .body = root,
            .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            .replayed = site.in_block,
        };
        const at = if (site.in_block) site.fixed else null;
        const node = try self.describeDefinition(key, null, instance, .{}, &.{}, at);
        return self.siteNode(node, key);
    }

    /// Either the description or the reason the walk stopped.
    fn outcomeOf(self: *Reifier, result: Error!ConstNodeId) Allocator.Error!Outcome {
        const node = result catch |err| switch (err) {
            error.Rejected => return .{ .rejected = self.walk.rejection.? },
            else => |e| return e,
        };
        return .{ .reified = node };
    }

    /// Describe what each argument of a template call fixes, or say why one
    /// is not fixed. The caller releases `out` with `releaseTemplateArgs`.
    ///
    /// The arguments are written where the call is, so this runs over the
    /// calling module's stores even when the template itself is imported.
    pub fn reifyConstants(
        self: *Reifier,
        args: []const CheckedExprId,
        out: *std.ArrayList(TemplateArg),
        gpa: Allocator,
    ) Allocator.Error!?Rejection {
        out.clearRetainingCapacity();
        for (args) |arg_id| {
            const value = self.templateArg(arg_id) catch |err| switch (err) {
                error.Rejected => return self.walk.rejection.?,
                else => |e| return e,
            };
            try out.append(gpa, value);
        }
        return null;
    }

    /// Release what a template call's function arguments resolved.
    pub fn releaseTemplateArgs(self: *Reifier, args: []TemplateArg) void {
        for (args) |*arg| switch (arg.*) {
            .value => {},
            .callee => |*target| {
                if (target.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
                self.releaseBound(target.bound);
                target.bound = &.{};
            },
        };
    }

    /// A function argument has no node, so the template's parameter binds to
    /// the definition the argument names, the way a call's function argument
    /// binds its callee's parameter.
    fn templateArg(self: *Reifier, arg_id: CheckedExprId) Error!TemplateArg {
        const arg = self.bodies.expr(arg_id);
        if (self.functionOf(arg.ty) == null) return .{ .value = try self.constantNode(arg_id) };
        return .{ .callee = try self.templateCallee(arg_id) };
    }

    /// The definition a function argument of a template call names.
    ///
    /// A lambda written as the argument, or one a block binds, is lifted into
    /// a row that reads the block around it the way a lambda at a `Code`
    /// position does: the call is fixed while the compiler runs, and so is
    /// every statement the row replays.
    fn templateCallee(self: *Reifier, arg_id: CheckedExprId) Error!CalleeTarget {
        const arg = self.bodies.expr(arg_id);
        const region = arg.source_region;
        switch (arg.data) {
            .lambda, .closure => return .{
                .key = .{ .artifact = self.artifact.bytes, .body = arg_id, .replayed = true },
                .spelling = try self.lambdaArgumentSpelling(arg_id, region),
                .reader = self,
                .lifted = true,
                .at = arg.ty,
            },
            .lookup_local => |local| {
                const binder = self.bodies.patternBinderForCheckedPattern(local.pattern) orelse
                    return self.rejectError(.unresolved_reference, region, "this argument");
                if (self.blockLambdaOf(binder)) |lambda| {
                    const binding = Binding{ .binder = binder, .name = self.binderName(binder), .kind = .{ .function = lambda } };
                    var lifted = (try self.liftedTarget(binding, binder, arg.ty, region)).definition;
                    lifted.key.replayed = true;
                    lifted.captures = &.{};
                    lifted.at = arg.ty;
                    return lifted;
                }
                return self.passedCallee(arg_id, region);
            },
            .lookup_external, .lookup_required => return self.passedCallee(arg_id, region),
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return self.rejectError(.unsupported_expression, region, "a function value that names no definition"),
        }
    }

    /// The lambda a block binds a name to, or null for a name no block binds
    /// to a lambda. Only a block's `decl` records a defining statement.
    fn blockLambdaOf(self: *Reifier, binder: checked.PatternBinderId) ?CheckedExprId {
        const statement_id = self.bodies.patternBinder(binder).defining_statement orelse return null;
        const statement = self.bodies.statement(statement_id).data;
        if (statement != .decl) return null;
        return if (self.lambdaOf(statement.decl.expr) != null) statement.decl.expr else null;
    }

    /// Describe the lambda `template` returns, with `values` written into it.
    ///
    /// `template` is the whole `Code`-returning function: its parameters are
    /// the compile-time ones, and the lambda it returns is what the stage
    /// reads. `values` is one per parameter, in order: a value with no free
    /// names in it, or the definition a function argument names.
    pub fn reifyTemplateCall(
        self: *Reifier,
        template: CheckedExprId,
        values: []const TemplateArg,
        region: base.Region,
    ) Allocator.Error!Outcome {
        return self.outcomeOf(self.templateSiteNode(template, values, region));
    }

    /// A template call's site. The lambda a template returns is not a
    /// definition of any module, so nothing names it and it takes no entry of
    /// its own; what it calls still does.
    fn templateSiteNode(
        self: *Reifier,
        template: CheckedExprId,
        values: []const TemplateArg,
        region: base.Region,
    ) Error!ConstNodeId {
        const outer_base = self.walk.frame_base;
        self.walk.frame_base = self.walk.callees.items.len;
        defer {
            self.walk.callees.shrinkRetainingCapacity(self.walk.frame_base);
            self.walk.frame_base = outer_base;
        }

        const node = try self.templateCallNode(template, values, region);
        var rows = try self.definitionRows(self.walk.callees.items[self.walk.frame_base..], region);
        defer rows.deinit(self.gpa);
        return self.recordOf(&rows, node);
    }

    fn templateCallNode(
        self: *Reifier,
        template: CheckedExprId,
        values: []const TemplateArg,
        region: base.Region,
    ) Error!ConstNodeId {
        const lambda = try self.lambdaData(template);
        if (lambda.args.len != values.len) {
            return self.reject(.unsupported_expression, region, "a template called with the wrong number of arguments");
        }

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        // The site owns each callee; the walk borrows it, and a call on the
        // parameter copies it the way a call on a bound row parameter does.
        var bound = std.ArrayList(BoundCallee).empty;
        defer bound.deinit(self.gpa);
        for (lambda.args, values, 0..) |pattern_id, value, index| {
            switch (value) {
                .value => |node| _ = try self.bind(pattern_id, .{ .constant = node }, region),
                .callee => |target| {
                    _ = try self.bind(pattern_id, .{ .callee = @intCast(bound.items.len) }, region);
                    try bound.append(self.gpa, .{ .param = @intCast(index), .target = target });
                },
            }
        }

        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        self.bound = bound.items;
        self.bound_lambda = null;
        defer {
            self.bound = outer_bound;
            self.bound_lambda = outer_bound_lambda;
        }
        return self.lambdaNode(lambda.body);
    }

    /// Whether the walk describes this expression with no free names in it.
    ///
    /// A template's argument has to be one of these, because the value is
    /// written into the description where a name would otherwise stand. A
    /// literal qualifies, and so does an aggregate every part of which does.
    /// The forms listed are the ones `irNodeAs` builds without reading the
    /// staged scope, which is what keeps this and the walk in step.
    fn isConstantForm(self: *Reifier, expr_id: CheckedExprId) Allocator.Error!bool {
        return switch (self.bodies.expr(expr_id).data) {
            // A literal of the author's own type describes as the conversion
            // call beside it, which reads no staged name.
            .numeral, .str_from_quote, .str_segment, .bytes_literal, .empty_list, .empty_record => true,
            .str => |segments| try self.everyPartIsConstant(segments),
            .list, .tuple => |items| try self.everyPartIsConstant(items),
            .record => |record| blk: {
                for (record.fields) |field| {
                    if (!try self.isConstantForm(field.value)) break :blk false;
                }
                break :blk true;
            },
            .nominal => |nominal| try self.isConstantForm(nominal.backing_expr),
            .row_coerce => |coerce| try self.isConstantForm(coerce.value),
            .tag => |tag_expr| try self.everyPartIsConstant(tag_expr.args),
            .zero_argument_tag => true,
            // A name is the form the value it holds is, which is what lets a
            // template argument be written as one.
            .lookup_local => |lookup| try self.nameHoldsConstant(lookup.resolved),
            .lookup_external, .lookup_required => |reference| try self.nameHoldsConstant(reference),
            .anno_only,
            .binop,
            .block,
            .break_,
            .call,
            .closure,
            .code_from_lambda,
            .crash,
            .dbg,
            .dispatch_call,
            .ellipsis,
            .expect,
            .expect_err,
            .field_access,
            .for_,
            .hosted_lambda,
            .if_,
            // The checker binds every interpolated value to a name of its
            // own, so no interpolated literal is a constant form however it
            // is written.
            .interpolation,
            .lambda,
            .match_,
            .method_eq,
            .pending,
            .return_,
            .run_low_level,
            .runtime_error,
            .structural_eq,
            .structural_hash,
            .tuple_access,
            .type_dispatch_call,
            .unary_minus,
            .unary_not,
            => false,
        };
    }

    /// Whether the value a name holds is a constant form.
    ///
    /// The walk marks the definition while it asks, so a definition that
    /// reaches itself answers no on the repeat rather than recursing forever.
    fn nameHoldsConstant(self: *Reifier, resolved: ?checked.ResolvedValueRefId) Allocator.Error!bool {
        const definition = try self.constantDefinition(resolved) orelse return false;
        const reader = definition.reader;
        if (reader.folding.contains(definition.body)) return false;
        try reader.folding.put(reader.gpa, definition.body, {});
        defer _ = reader.folding.remove(definition.body);
        return try reader.isConstantForm(definition.body);
    }

    fn everyPartIsConstant(self: *Reifier, parts: []const CheckedExprId) Allocator.Error!bool {
        for (parts) |part| {
            if (!try self.isConstantForm(part)) return false;
        }
        return true;
    }

    /// The value an argument fixed at compile time becomes.
    fn constantNode(self: *Reifier, arg_id: CheckedExprId) Error!ConstNodeId {
        const arg = self.bodies.expr(arg_id);
        if (!try self.isConstantForm(arg_id)) {
            return self.reject(.argument_not_constant, arg.source_region, "");
        }
        // A literal form the walk still refuses, a numeral whose type stayed
        // open among them, keeps the reason the walk recorded: it says more
        // about the argument than this one would.
        return self.irNode(arg_id);
    }

    // Ir //

    /// The parameters and body of the lambda an expression is, looking through
    /// a closure whose captures a template call already fixed.
    fn lambdaData(self: *Reifier, expr_id: CheckedExprId) Error!LambdaData {
        const expr = self.bodies.expr(expr_id);
        return switch (expr.data) {
            .lambda => |l| l,
            .closure => |closure| blk: {
                break :blk switch (self.bodies.expr(closure.lambda).data) {
                    .lambda => |inner| inner,
                    .pending,
                    .numeral,
                    .str_from_quote,
                    .code_from_lambda,
                    .str_segment,
                    .str,
                    .row_coerce,
                    .bytes_literal,
                    .lookup_local,
                    .lookup_external,
                    .lookup_required,
                    .list,
                    .empty_list,
                    .tuple,
                    .match_,
                    .if_,
                    .call,
                    .record,
                    .empty_record,
                    .block,
                    .tag,
                    .nominal,
                    .zero_argument_tag,
                    .closure,
                    .binop,
                    .unary_minus,
                    .unary_not,
                    .field_access,
                    .dispatch_call,
                    .interpolation,
                    .structural_eq,
                    .structural_hash,
                    .method_eq,
                    .type_dispatch_call,
                    .tuple_access,
                    .runtime_error,
                    .crash,
                    .dbg,
                    .expect_err,
                    .expect,
                    .ellipsis,
                    .anno_only,
                    .break_,
                    .return_,
                    .for_,
                    .hosted_lambda,
                    .run_low_level,
                    => return self.rejectError(.unsupported_expression, expr.source_region, "a closure"),
                };
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return self.rejectError(.unsupported_expression, expr.source_region, exprFormName(expr.data)),
        };
    }

    /// Where a lambda's captures go.
    const CaptureRule = enum {
        /// The lambda is described where it stands, inside a description that
        /// already binds what it captured, so a reference to a captured name
        /// describes as the parameter or local it is.
        in_scope,
        /// The row is described on its own, with none of the scope around it,
        /// so what the lambda captured arrives as a leading parameter and
        /// every call site passes it first.
        parameter,
    };

    fn lambdaNode(self: *Reifier, expr_id: CheckedExprId) Error!ConstNodeId {
        return self.lambdaNodeAs(expr_id, .in_scope, null);
    }

    /// Which bound callee fixed one parameter of the row being walked, if the
    /// call fixed it at all.
    fn boundCallee(self: *Reifier, index: usize) ?u32 {
        for (self.bound, 0..) |entry, slot| {
            if (entry.param == index) return @intCast(slot);
        }
        return null;
    }

    /// `at` is the function type to read the signature from, for a lambda
    /// whose node does not hold one. A lambda written at a `Code(f)` position
    /// is the case: its node holds the `Code`, so the walk is told the `f`.
    fn lambdaNodeAs(
        self: *Reifier,
        expr_id: CheckedExprId,
        captures: CaptureRule,
        at: ?CheckedTypeId,
    ) Error!ConstNodeId {
        const expr = self.bodies.expr(expr_id);
        const region = expr.source_region;
        const lambda = try self.lambdaData(expr_id);
        const captured = self.capturesOf(expr_id);

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        const fn_ty_id = at orelse self.stagedFunctionTypeId(expr);
        const staged_fn = self.functionOf(fn_ty_id) orelse
            return self.reject(.unsupported_type, region, "a reified value that is not a function");
        // A stage runs this description during `roc build`, where an effect has
        // nowhere to happen. `tyNode` refuses an effectful function everywhere
        // else; the staged lambda's own type is the one that never reaches it.
        if (staged_fn.kind == .effectful) {
            return self.reject(.effect, region, "an effectful function");
        }
        const param_tys = staged_fn.args;
        if (param_tys.len != lambda.args.len) {
            return self.reject(.unsupported_expression, region, "lambda");
        }

        var params = std.ArrayList(ConstNodeId).empty;
        defer params.deinit(self.gpa);
        var arg_tys = std.ArrayList(ConstNodeId).empty;
        defer arg_tys.deinit(self.gpa);
        var destructures = std.ArrayList(Destructure).empty;
        defer destructures.deinit(self.gpa);

        if (captures == .parameter) {
            for (captured) |capture| {
                const pattern = self.bodies.pattern(capture.pattern);
                const name = try self.bindParam(capture.pattern, pattern.source_region);
                const ty = try self.tyNode(pattern.ty, pattern.source_region);
                try params.append(self.gpa, try self.namedTypeEntry(name, ty));
                try arg_tys.append(self.gpa, ty);
            }
        } else {
            // A capture of a name the staged scope already holds needs nothing
            // at run time: a template call fixed it to a literal, or a lambda
            // around this one binds it and `lookupNode` describes the
            // reference where it is written. A name from outside the staged
            // function stays the refusal it has always been.
            for (captured) |capture| {
                if (self.capturedInScope(capture.pattern)) continue;
                if (self.replayStatement(capture.pattern) != null) continue;
                return self.reject(.capture, region, self.capturedName(capture.pattern));
            }
        }

        for (lambda.args, param_tys, 0..) |pattern_id, param_ty, index| {
            // A parameter the call fixed to a definition is not a parameter of
            // the row: a call on it names that definition, and the call site
            // passes nothing for it.
            if (self.bound_lambda == expr_id) {
                if (self.boundCallee(index)) |slot| {
                    _ = try self.bind(pattern_id, .{ .callee = slot }, region);
                    continue;
                }
            }
            const name = try self.bindParamPattern(pattern_id, &destructures, region);
            const ty = try self.tyNode(param_ty, region);
            try params.append(self.gpa, try self.namedTypeEntry(name, ty));
            try arg_tys.append(self.gpa, ty);
        }

        const params_list = try self.store.append(.{ .list = .{ .nodes = params.items } });
        // A lambda written inside a loop is a function of its own, so a
        // `return` in it leaves the lambda rather than the loop.
        const outer_loop = self.loop;
        self.loop = null;
        defer self.loop = outer_loop;

        const ret_meta = try self.metaNode(try self.tyNode(staged_fn.ret, region), region);
        const walked = try self.wrapDestructures(destructures.items, try self.tailNode(lambda.body, ret_meta), ret_meta);
        const body = if (self.replay) |replay|
            if (replay.root == expr_id) try self.replayedNode(replay, walked, ret_meta, region) else walked
        else
            walked;
        // The node's own type, as on every other node: the function type the
        // signature reads from, not the body's. A row whose signature this
        // walk changed, by taking captures as parameters or by dropping ones
        // the call fixed, has one the checker never solved, so it is built
        // from the parameter types gathered here.
        const fn_ty = if (params.items.len == lambda.args.len and captures == .in_scope)
            try self.tyNode(fn_ty_id, region)
        else blk: {
            const args_list = try self.store.append(.{ .list = .{ .nodes = arg_tys.items } });
            break :blk try self.tag("Fn", &.{ args_list, try self.tyNode(staged_fn.ret, region) });
        };
        const meta = try self.metaNode(fn_ty, region);
        return self.tag("Lambda", &.{ params_list, body, meta });
    }

    /// One `Lambda` for a curried definition, with both lambdas' parameters
    /// gathered into one signature and the inner body as the body.
    ///
    /// The description is first order, so a definition that hands back a
    /// function and the call that runs it are one row and one `Call`. An
    /// inner parameter that repeats an outer one binds second, and so wins,
    /// which is the rule a nested `Lambda` already sets.
    fn curriedLambdaNode(self: *Reifier, expr_id: CheckedExprId) Error!ConstNodeId {
        const expr = self.bodies.expr(expr_id);
        const region = expr.source_region;

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        var params = std.ArrayList(ConstNodeId).empty;
        defer params.deinit(self.gpa);
        var arg_tys = std.ArrayList(ConstNodeId).empty;
        defer arg_tys.deinit(self.gpa);
        var destructures = std.ArrayList(Destructure).empty;
        defer destructures.deinit(self.gpa);

        const outer = try self.bindLambdaParams(expr_id, &params, &arg_tys, &destructures, region);
        const inner = try self.bindLambdaParams(outer.body, &params, &arg_tys, &destructures, region);

        const params_list = try self.store.append(.{ .list = .{ .nodes = params.items } });
        const outer_loop = self.loop;
        self.loop = null;
        defer self.loop = outer_loop;

        const ret = try self.tyNode(inner.fn_ty.ret, region);
        const ret_meta = try self.metaNode(ret, region);
        const body = try self.wrapDestructures(destructures.items, try self.tailNode(inner.body, ret_meta), ret_meta);
        const args_list = try self.store.append(.{ .list = .{ .nodes = arg_tys.items } });
        const fn_ty = try self.tag("Fn", &.{ args_list, ret });
        const meta = try self.metaNode(fn_ty, region);
        return self.tag("Lambda", &.{ params_list, body, meta });
    }

    /// What one level of a curried definition contributed: the body under it,
    /// and the function type its parameters came from.
    const BoundLambda = struct {
        body: CheckedExprId,
        fn_ty: checked.CheckedFunctionType,
    };

    /// Bind one lambda's parameters into the staged scope, appending a named
    /// type entry and a parameter type to the signature being gathered.
    fn bindLambdaParams(
        self: *Reifier,
        expr_id: CheckedExprId,
        params: *std.ArrayList(ConstNodeId),
        arg_tys: *std.ArrayList(ConstNodeId),
        destructures: *std.ArrayList(Destructure),
        region: base.Region,
    ) Error!BoundLambda {
        const expr = self.bodies.expr(expr_id);
        const lambda = try self.lambdaData(expr_id);
        const fn_ty_id = self.stagedFunctionTypeId(expr);
        const fn_ty = self.functionOf(fn_ty_id) orelse
            return self.rejectError(.unsupported_type, region, "a reified value that is not a function");
        if (fn_ty.kind == .effectful) {
            return self.rejectError(.effect, region, "an effectful function");
        }
        if (fn_ty.args.len != lambda.args.len) {
            return self.rejectError(.unsupported_expression, region, "lambda");
        }
        for (lambda.args, fn_ty.args) |pattern_id, param_ty| {
            const name = try self.bindParamPattern(pattern_id, destructures, region);
            const ty = try self.tyNode(param_ty, region);
            try params.append(self.gpa, try self.namedTypeEntry(name, ty));
            try arg_tys.append(self.gpa, ty);
        }
        return .{ .body = lambda.body, .fn_ty = fn_ty };
    }

    /// The function type of the lambda being described.
    ///
    /// A template's lambda is the node the `Code` landed on, so its own type is
    /// the `Code` rather than the function inside it. The lambda the closure
    /// wraps keeps the function type, and that is the one the signature reads.
    fn stagedFunctionTypeId(self: *Reifier, expr: checked.CheckedExpr) CheckedTypeId {
        if (self.functionOf(expr.ty) != null) return expr.ty;
        if (expr.data != .closure) return expr.ty;
        return self.bodies.expr(expr.data.closure.lambda).ty;
    }

    fn irNode(self: *Reifier, expr_id: CheckedExprId) Error!ConstNodeId {
        return self.irNodeAs(expr_id, null);
    }

    /// `ty_override` carries a nominal's own type down to the expression that
    /// builds its backing, so `Vec2.((x, y))` stays a `Named` tuple rather than
    /// an anonymous one.
    fn irNodeAs(self: *Reifier, expr_id: CheckedExprId, ty_override: ?TypeOverride) Error!ConstNodeId {
        // A construct lifted out past this expression stands here as whatever
        // the branch being described gives it.
        for (self.lifts.items) |lifted| {
            if (lifted.expr == expr_id) return lifted.node;
        }

        const expr = self.bodies.expr(expr_id);
        const region = expr.source_region;
        const subject_ty = if (ty_override) |override| override.checked else expr.ty;
        const ty = if (ty_override) |override| override.node else try self.tyNode(expr.ty, region);
        const meta = try self.metaNode(ty, region);

        return switch (expr.data) {
            .numeral => |data| try self.literalNode(data, expr.ty, ty, meta, region),
            .str_segment => |literal| blk: {
                const text = try self.strNode(self.bodies.stringLiteral(literal));
                const lit = try self.tag("Str", &.{text});
                break :blk try self.tag("Lit", &.{ lit, meta });
            },
            .str => |segments| blk: {
                if (segments.len == 1) break :blk try self.irNode(segments[0]);
                break :blk try self.interpolatedNode(segments, meta);
            },
            .lookup_local => |lookup| try self.lookupNode(lookup.pattern, lookup.resolved, meta, region),
            .match_ => |match_expr| try self.matchNode(match_expr.cond, match_expr.branches, false, meta),
            .block => |block| try self.blockNode(block.statements, block.final_expr, false, meta, region),
            .binop => |binop| blk: {
                const name = binopName(binop.op) orelse
                    break :blk try self.reject(.unsupported_expression, region, "this operator");
                const lhs = try self.irNode(binop.lhs);
                const rhs = try self.irNode(binop.rhs);
                const op = try self.strNode(name);
                break :blk try self.tag("Binop", &.{ op, lhs, rhs, meta });
            },
            .unary_minus => |operand| blk: {
                const inner = try self.irNode(operand);
                const op = try self.strNode("neg");
                break :blk try self.tag("Unary", &.{ op, inner, meta });
            },
            .unary_not => |operand| blk: {
                const inner = try self.irNode(operand);
                const op = try self.strNode("not");
                break :blk try self.tag("Unary", &.{ op, inner, meta });
            },
            .if_ => |if_expr| try self.ifNode(if_expr.branches, if_expr.final_else, false, meta),
            .tuple => |items| blk: {
                const nodes = try self.irNodes(items);
                defer self.gpa.free(nodes);
                const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
                break :blk try self.tag("MakeTuple", &.{ list, meta });
            },
            .list => |items| blk: {
                const nodes = try self.irNodes(items);
                defer self.gpa.free(nodes);
                const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
                break :blk try self.tag("MakeList", &.{ list, meta });
            },
            .empty_list => blk: {
                const list = try self.store.append(.{ .list = .{ .nodes = &.{} } });
                break :blk try self.tag("MakeList", &.{ list, meta });
            },
            .record => |record| try self.recordNode(record.fields, record.ext, subject_ty, meta, region),
            .empty_record => blk: {
                const list = try self.store.append(.{ .list = .{ .nodes = &.{} } });
                break :blk try self.tag("MakeRecord", &.{ list, meta });
            },
            .tuple_access => |access| blk: {
                const receiver = try self.irNode(access.tuple);
                const index = try self.store.append(.{ .scalar = .{ .u64 = access.elem_index } });
                break :blk try self.tag("Index", &.{ receiver, index, meta });
            },
            .field_access => |access| try self.fieldAccessNode(access.receiver, access.segments, meta, region),
            // A crash the compiler wrote carries its message as a literal,
            // where a written one carries an expression, so this arm lifts the
            // literal into the `Ir` the node holds.
            .crash => |literal| blk: {
                const text = try self.strNode(self.bodies.stringLiteral(literal));
                const lit = try self.tag("Str", &.{text});
                const message = try self.tag("Lit", &.{ lit, meta });
                break :blk try self.tag("Crash", &.{ message, meta });
            },
            .dispatch_call => |plan_id| try self.dispatchNode(plan_id, meta, region),
            // `Type.method(args)` resolves to the same plan a value dispatch
            // leaves behind, and the plan names the dispatcher, so the two
            // describe through one arm. It is how a derived codec is reached:
            // `Shape.encoder_for(format)` dispatches on the type, not a value.
            .type_dispatch_call => |plan_id| try self.dispatchNode(plan_id, meta, region),
            // A hand-written `is_eq` is an ordinary method call; it only shares
            // a checked variant group with the two derived forms.
            .method_eq => |plan_id| try self.methodEqNode(plan_id, meta, region),
            .structural_eq => |eq| try self.structuralEqNode(eq.lhs, eq.rhs, eq.negated, meta, region),
            .structural_hash => |hash| try self.structuralHashNode(hash.value, hash.hasher, meta, region),
            .dbg => try self.reject(.effect, region, "dbg"),
            .hosted_lambda => try self.reject(.effect, region, "a hosted function"),
            .nominal => |nominal| try self.irNodeAs(
                nominal.backing_expr,
                .{ .node = ty, .checked = subject_ty },
            ),
            // A value used at a wider tag union than its own. The value keeps
            // its own row and the node carries the wider one, because moving
            // a value between two unions renumbers its tag wherever a target
            // numbers tags per union, and a translator must see where.
            .row_coerce => |coerce| try self.tag("Widen", &.{ try self.irNode(coerce.value), meta }),
            .tag => |tag_expr| try self.tagNode(tag_expr.name, tag_expr.args, subject_ty, meta, region),
            .zero_argument_tag => |tag_expr| try self.tagNode(tag_expr.name, &.{}, subject_ty, meta, region),
            .call => |call| try self.callNode(call.func, call.args, meta, region),
            // A lambda written inside the staged function is another `Lambda`,
            // and its scope nests inside the one already open, so the same
            // walk describes it. `lambdaNode` reads the type from the lambda
            // rather than from `meta`, because a closure's own node carries
            // the captures and the lambda under it carries the signature.
            .lambda, .closure => try self.lambdaNode(expr_id),
            // A name of another module holds no binding in the staged scope,
            // so the only description it has is the value it was fixed to.
            .lookup_external, .lookup_required => |reference| blk: {
                if (try self.foldedConstant(reference, region)) |folded| break :blk folded;
                break :blk try self.reject(.unsupported_expression, region, exprFormName(expr.data));
            },
            // A quoted literal of the author's own type is the `from_quote`
            // call the checker wrote, named for the same reason a
            // `from_numeral` call is: the conversion may parse or validate.
            .str_from_quote => |quote| blk: {
                const plan_id = quote.plan orelse
                    break :blk try self.reject(.unresolved_reference, region, "this quoted literal");
                break :blk try self.dispatchNode(plan_id, meta, region);
            },
            // An interpolated literal of the author's own type is the
            // `from_interpolation` call the checker wrote, named for the same
            // reason a `from_numeral` call is: the method decides what the
            // pieces become, and a translator handed only the pieces would be
            // guessing at it.
            .interpolation => |interpolation| blk: {
                const plan_id = interpolation.plan orelse
                    break :blk try self.reject(.unresolved_reference, region, "this interpolated literal");
                break :blk try self.dispatchNode(plan_id, meta, region);
            },
            // An embedded file, which is the one expression a `List(U8)`
            // literal is written as.
            .bytes_literal => |literal| blk: {
                const bytes = try self.bytesNode(self.bodies.stringLiteral(literal));
                const lit = try self.tag("Bytes", &.{bytes});
                break :blk try self.tag("Lit", &.{ lit, meta });
            },
            .pending,
            .code_from_lambda,
            .runtime_error,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            => try self.reject(.unsupported_expression, region, exprFormName(expr.data)),
            // A written `crash` arrives as an intrinsic rather than as the
            // checked `.crash` a compiler-written one does, and it is the one
            // intrinsic the description has a node for. The op is what names
            // it: the message is the author's text and says nothing.
            .run_low_level => |run| blk: {
                if (run.op != .crash or run.args.len != 1) {
                    break :blk try self.reject(.unsupported_expression, region, exprFormName(expr.data));
                }
                const message = try self.irNode(run.args[0]);
                break :blk try self.tag("Crash", &.{ message, meta });
            },
        };
    }

    /// `==` or `!=` on a type whose `is_eq` is written rather than derived.
    ///
    /// Which of the two the author wrote rides on the dispatch plan, not on
    /// the checked node, so the walk reads it there. Lowering reads the same
    /// flag and negates the call's result with it
    /// (`src/postcheck/boxy/lower.zig:18226`).
    fn methodEqNode(
        self: *Reifier,
        plan_id: ?static_dispatch.StaticDispatchPlanId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const compare = try self.dispatchNode(plan_id, meta, region);
        // `dispatchNode` refuses an absent plan, so one is present here.
        const plan = self.plans.plans[@backingInt(plan_id.?)];
        const negated = switch (plan.result_mode) {
            .equality => |eq| eq.negated,
            .value, .hash, .parser_for, .encoder_for, .map, .map_effectful => false,
        };
        if (!negated) return compare;
        // The derived half writes the same shape, and `is_not_eq` is not a
        // name a dispatch can carry, so both halves describe as one `Unary`.
        return self.tag("Unary", &.{ try self.strNode("not"), compare, meta });
    }

    /// A derived `==`. The checker leaves no dispatch plan behind, because the
    /// recipe is fixed by the type, so the reifier emits the comparison that
    /// recipe performs.
    fn structuralEqNode(
        self: *Reifier,
        lhs_id: CheckedExprId,
        rhs_id: CheckedExprId,
        negated: bool,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const operand_ty = self.bodies.expr(lhs_id).ty;
        const lhs = try self.irNode(lhs_id);
        const rhs = try self.irNode(rhs_id);
        const compare = try self.structuralEqOver(lhs, rhs, operand_ty, meta, region);
        if (!negated) return compare;
        return self.tag("Unary", &.{ try self.strNode("not"), compare, meta });
    }

    /// The comparison a derived `==` performs on one type, over two operands
    /// already described as `Ir`.
    ///
    /// An aggregate names each operand once per component. A `ConstNodeId` is a
    /// shared reference, so naming one twice costs one id rather than a second
    /// subtree, and a staged body is pure, so a stage that would pay for the
    /// repetition in its own target can bind the operand itself.
    fn structuralEqOver(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        type_id: CheckedTypeId,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        return self.structuralEqOverAs(lhs, rhs, type_id, null, bool_meta, region);
    }

    /// `display_ty` plays the part `ty_override` plays in `irNodeAs`: a
    /// nominal hands its own type down to the comparison over its backing, so
    /// a pattern the comparison writes names `Color` rather than the union
    /// `Color` wraps. Only a tag union reads it, because only a tag union
    /// writes patterns.
    fn structuralEqOverAs(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        type_id: CheckedTypeId,
        display_ty: ?CheckedTypeId,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        return switch (self.types.payload(type_id)) {
            .alias => |alias| self.structuralEqOverAs(lhs, rhs, alias.backing, display_ty, bool_meta, region),
            .nominal => |nominal| self.nominalEqOver(lhs, rhs, nominal, type_id, bool_meta, region),
            .record => |record| self.fieldsEqOver(lhs, rhs, record.fields, bool_meta, region),
            .tuple => |elements| self.elementsEqOver(lhs, rhs, elements, bool_meta, region),
            .tag_union => |tag_union| self.tagUnionEqOver(
                lhs,
                rhs,
                tag_union,
                display_ty orelse type_id,
                bool_meta,
                region,
            ),
            // One inhabitant, so both operands hold it.
            .empty_record => self.trueNode(bool_meta),
            // No inhabitant, so there is no pair of operands to compare.
            .empty_tag_union => self.reject(.unsupported_type, region, "derived equality on an empty tag union"),
            .flex, .rigid => self.reject(.unresolved_type, region, "a type variable"),
            .pending, .err => self.reject(.unresolved_type, region, "an unresolved type"),
            .function => self.reject(.unsupported_type, region, "derived equality on a function"),
        };
    }

    /// What a nominal's declaration says about one method.
    const NominalMethod = union(enum) {
        /// The method is written, and this is the call the derivation makes.
        written: ConstNodeId,
        /// The compiler derives it, so the value is its backing's.
        derived,
        /// No module in reach declares it.
        undeclared,
    };

    /// The call a nominal's own `is_eq` or `to_hash` takes, when it writes one.
    ///
    /// The compiler dispatches to a nominal's own method before it looks at the
    /// nominal's representation, and a derivation leaves no dispatch plan, so
    /// this is the one place the walk resolves a method itself. The method
    /// registries answer it, and they say which of the two it is: a procedure
    /// target names a written body, and a structural target is the derivation
    /// recipe, which is the signal to expand the backing.
    ///
    /// A written body the walk cannot reach keeps the bare name, the way a
    /// dispatch to one does: the name is what a translator resolves against
    /// its own target, and it is still the method Roc calls.
    ///
    /// `receiver` is the type of the value the derivation is walking, which is
    /// what fixes a generic method's quantified variables where a call site
    /// would have fixed them off its edge.
    fn nominalMethod(
        self: *Reifier,
        method: []const u8,
        nominal: checked.CheckedNominalType,
        receiver: CheckedTypeId,
        args: []const ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!NominalMethod {
        const target = self.walk.foreign.findMethod(self.foreignNominal(nominal), method) orelse return .undeclared;
        if (std.meta.activeTag(target.kind) == .structural) return .derived;
        return .{ .written = try self.writtenMethodCall(method, nominal, receiver, target, args, meta, region) };
    }

    /// A nominal named the way the registries of any module can read it.
    fn foreignNominal(self: *Reifier, nominal: checked.CheckedNominalType) ForeignNominal {
        return .{
            .module = self.names.moduleIdentityBytes(nominal.origin_module),
            .source_decl = nominal.source_decl,
            .builtin = builtinMethodOwner(nominal.builtin),
        };
    }

    /// The call to a method a nominal writes, with its body described into
    /// the table when the walk can reach it and the bare name when it cannot.
    fn writtenMethodCall(
        self: *Reifier,
        method: []const u8,
        nominal: checked.CheckedNominalType,
        receiver: CheckedTypeId,
        target: static_dispatch.MethodTarget,
        args: []const ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const spelled = try std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ self.names.typeNameText(nominal.name), method });
        defer self.gpa.free(spelled);
        const name = self.describedMethod(target, receiver, spelled, region) catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.Rejected => spelled,
        };
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return self.tag("Call", &.{ try self.strNode(name), list, meta });
    }

    /// `Str.inspect(value)`: the call to the subject's own `to_inspect` when
    /// that method is the inspect override, and otherwise a `Derived` left for
    /// the stage.
    ///
    /// The default rendering is not expanded. It is Roc's debugging format and
    /// a translator targets its own, the argument that keeps a codec symbolic,
    /// and expanding it would write an opaque nominal's backing into the
    /// description. The override is the subject's alone: a component's own
    /// `to_inspect` belongs to the default rendering around it, so it stays
    /// inside the `Derived`.
    fn inspectNode(
        self: *Reifier,
        operand: CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const value_ty = self.bodies.expr(operand).ty;
        const value = try self.irNode(operand);
        var subject_ty = value_ty;
        while (true) switch (self.types.payload(subject_ty)) {
            .alias => |alias| subject_ty = alias.backing,
            .nominal => |nominal| {
                const target = self.walk.foreign.findInspectOverride(self.foreignNominal(nominal)) orelse break;
                return self.writtenMethodCall("to_inspect", nominal, subject_ty, target, &.{value}, meta, region);
            },
            .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => break,
        };
        return self.derivedNode("to_inspect", value_ty, &.{value}, meta, region);
    }

    /// The intrinsic the checker recorded for a call's callee, when the callee
    /// is a procedure the compiler implements.
    fn calleeIntrinsic(self: *Reifier, func: CheckedExprId) ?checked.IntrinsicId {
        const resolved = switch (self.bodies.expr(func).data) {
            .lookup_external, .lookup_required => |reference| reference orelse return null,
            .lookup_local => |local| local.resolved orelse return null,
            .pending, .numeral, .str_from_quote, .code_from_lambda, .str_segment, .str, .bytes_literal, .list, .empty_list, .tuple, .match_, .if_, .call, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .unary_not, .field_access, .dispatch_call, .interpolation, .structural_eq, .structural_hash, .method_eq, .type_dispatch_call, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .row_coerce, .for_, .hosted_lambda, .run_low_level => return null,
        };
        return switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc => |use| use.intrinsic,
            .local_param, .local_value, .local_mutable_version, .pattern_binder, .local_proc, .selected_hoisted_const, .top_level_const, .imported_const, .hosted_proc, .platform_required_declaration, .platform_required_checked_error, .platform_required_const, .platform_required_proc, .promoted_top_level_proc => null,
        };
    }

    /// The name one nominal method takes, with its body described into the
    /// table when the walk can describe it.
    ///
    /// A walk that stopped leaves nothing behind, as `describedDispatch`
    /// leaves nothing: the frame's callees go back to what they were, so the
    /// table names no row that was never written, and the site's first refusal
    /// is still the one it reports.
    fn describedMethod(
        self: *Reifier,
        target: static_dispatch.MethodTarget,
        receiver: CheckedTypeId,
        spelled: []const u8,
        region: base.Region,
    ) Error![]const u8 {
        const callees = self.walk.callees.items.len;
        const rejection = self.walk.rejection;
        errdefer {
            self.walk.callees.shrinkRetainingCapacity(callees);
            self.walk.rejection = rejection;
        }
        const fixing: MethodFixing = .{ .receiver = self.resolvedType(receiver) };
        return switch (try self.methodTargetCallee(self, target, fixing, spelled, region)) {
            .definition => |found| try self.calledDefinition(.{ .definition = found }, region),
            .provided => |provided| provided,
            .spelled => spelled,
        };
    }

    /// A nominal is transparent in the IR: its value is its backing, so the
    /// comparison is the backing's, unless the nominal writes an `is_eq` of
    /// its own, which is the one the compiler calls.
    fn nominalEqOver(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        nominal: checked.CheckedNominalType,
        type_id: CheckedTypeId,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // A scalar builtin folds into the `Binop` the `Ir` already has a node
        // for, which is a better description than a call to the builtin's own
        // method. Every other builtin goes to the registry like any nominal.
        if (nominal.builtin) |builtin_nominal| {
            if (isScalarEq(builtin_nominal)) {
                return self.tag("Binop", &.{ try self.strNode("is_eq"), lhs, rhs, bool_meta });
            }
        }
        switch (try self.nominalMethod("is_eq", nominal, type_id, &.{ lhs, rhs }, bool_meta, region)) {
            .written => |call| return call,
            .derived => {},
            // The checker refuses `==` on a type that declares no equality, so
            // reaching here means the declaring module is out of the walk's
            // reach and the backing would be a guess.
            .undeclared => return self.reject(.unsupported_type, region, self.names.typeNameText(nominal.name)),
        }
        if (nominal.builtin != null) {
            return self.reject(.unsupported_type, region, "derived equality on this builtin type");
        }
        if (nominal.is_opaque) {
            return self.reject(.unsupported_type, region, self.names.typeNameText(nominal.name));
        }
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.reject(.unsupported_type, region, self.names.typeNameText(nominal.name));
        return self.structuralEqOverAs(lhs, rhs, backing, type_id, bool_meta, region);
    }

    /// A derived `==` over a tag union: the `match` that comparison is.
    ///
    /// Two values agree when they carry the same variant and its payloads
    /// agree, so the operands are paired and one branch per variant tests the
    /// pair. A union of more than one variant ends in a `_`, where every pair
    /// that disagrees on the variant lands.
    ///
    /// The compiler expands this rather than leaving it to a translator for
    /// the reason it expands the other two aggregates: a derived `==` is the
    /// compiler's recipe, and `Match`, `Variant` and `PatTuple` already
    /// describe every part of it.
    fn tagUnionEqOver(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        tag_union: checked.CheckedTagUnionType,
        display_ty: CheckedTypeId,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var variants = std.ArrayList(checked.CheckedTag).empty;
        defer variants.deinit(self.gpa);
        try self.collectVariants(&variants, tag_union.tags, tag_union.ext, region);
        // A chain that collects no variant describes a union nothing inhabits,
        // the same answer `empty_tag_union` gets.
        if (variants.items.len == 0) {
            return self.reject(.unsupported_type, region, "derived equality on an empty tag union");
        }

        const operand_ty = try self.tyNode(display_ty, region);
        const pair_tys = try self.store.append(.{ .list = .{ .nodes = &.{ operand_ty, operand_ty } } });
        const frame: EqBranchFrame = .{
            .operand = try self.metaNode(operand_ty, region),
            .pair = try self.metaNode(try self.tag("Tuple", &.{pair_tys}), region),
            .no_guard = try self.tag("NoGuard", &.{}),
        };
        const operands = try self.store.append(.{ .list = .{ .nodes = &.{ lhs, rhs } } });
        const subject = try self.tag("MakeTuple", &.{ operands, frame.pair });

        var branches = std.ArrayList(ConstNodeId).empty;
        defer branches.deinit(self.gpa);
        for (variants.items) |variant| {
            try branches.append(self.gpa, try self.variantEqBranch(variant, frame, bool_meta, region));
        }
        // One variant leaves no pair the branches above missed.
        if (variants.items.len > 1) {
            const anything = try self.tag("Anything", &.{frame.pair});
            const patterns = try self.store.append(.{ .list = .{ .nodes = &.{anything} } });
            const differ = try self.boolLiteralNode(false, bool_meta);
            try branches.append(self.gpa, try self.store.append(.{ .record = &.{ frame.no_guard, patterns, differ } }));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = branches.items } });
        return self.tag("Match", &.{ subject, list, bool_meta });
    }

    /// The nodes every branch of one tag union comparison shares.
    const EqBranchFrame = struct {
        /// The `Meta` a pattern over one operand carries.
        operand: ConstNodeId,
        /// The `Meta` the two operands carry once paired.
        pair: ConstNodeId,
        no_guard: ConstNodeId,
    };

    /// Room for `eq_lhs_` and the widest serial a `u32` reaches.
    const binder_name_max = "eq_lhs_".len + 10;

    /// The branch that compares one variant against itself.
    ///
    /// A payload is bound rather than read in place, because no `Ir` node
    /// reaches inside a variant. The name is generated: the compiler wrote
    /// this match, so no source holds a binder for it. The serial runs across
    /// the whole walk, so a union nested inside a union never rebinds a name
    /// its enclosing branch bound.
    fn variantEqBranch(
        self: *Reifier,
        variant: checked.CheckedTag,
        frame: EqBranchFrame,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const label = try self.strNode(self.names.tagLabelText(variant.name));
        const args = variant.argsSlice(self.types);

        const left_binders = try self.gpa.alloc(ConstNodeId, args.len);
        defer self.gpa.free(left_binders);
        const right_binders = try self.gpa.alloc(ConstNodeId, args.len);
        defer self.gpa.free(right_binders);

        var conjunction: ?ConstNodeId = null;
        for (args, 0..) |arg_ty, index| {
            const arg_meta = try self.metaNode(try self.tyNode(arg_ty, region), region);
            const serial = self.derived_binder_serial;
            self.derived_binder_serial += 1;

            var left_text: [binder_name_max]u8 = undefined;
            var right_text: [binder_name_max]u8 = undefined;
            const left_name = try self.strNode(std.fmt.bufPrint(&left_text, "eq_lhs_{d}", .{serial}) catch unreachable);
            const right_name = try self.strNode(std.fmt.bufPrint(&right_text, "eq_rhs_{d}", .{serial}) catch unreachable);

            left_binders[index] = try self.tag("Bind", &.{ left_name, arg_meta });
            right_binders[index] = try self.tag("Bind", &.{ right_name, arg_meta });

            const left_read = try self.tag("Local", &.{ left_name, arg_meta });
            const right_read = try self.tag("Local", &.{ right_name, arg_meta });
            const compare = try self.structuralEqOver(left_read, right_read, arg_ty, bool_meta, region);
            conjunction = try self.andNode(conjunction, compare, bool_meta);
        }

        const left_list = try self.store.append(.{ .list = .{ .nodes = left_binders } });
        const right_list = try self.store.append(.{ .list = .{ .nodes = right_binders } });
        const left_pattern = try self.tag("Variant", &.{ label, left_list, frame.operand });
        const right_pattern = try self.tag("Variant", &.{ label, right_list, frame.operand });
        const paired = try self.store.append(.{ .list = .{ .nodes = &.{ left_pattern, right_pattern } } });
        const pattern = try self.tag("PatTuple", &.{ paired, frame.pair });
        const patterns = try self.store.append(.{ .list = .{ .nodes = &.{pattern} } });
        // Every payload agreed, or the variant carries none.
        const value = conjunction orelse try self.trueNode(bool_meta);
        return self.store.append(.{ .record = &.{ frame.no_guard, patterns, value } });
    }

    fn fieldsEqOver(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        fields: []const checked.CheckedRecordField,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var conjunction: ?ConstNodeId = null;
        for (fields) |field| {
            const name = try self.strNode(self.names.recordFieldLabelText(field.name));
            const field_meta = try self.metaNode(try self.tyNode(field.ty, region), region);
            const left = try self.tag("Field", &.{ lhs, name, field_meta });
            const right = try self.tag("Field", &.{ rhs, name, field_meta });
            const compare = try self.structuralEqOver(left, right, field.ty, bool_meta, region);
            conjunction = try self.andNode(conjunction, compare, bool_meta);
        }
        return conjunction orelse self.trueNode(bool_meta);
    }

    fn elementsEqOver(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        elements: []const CheckedTypeId,
        bool_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var conjunction: ?ConstNodeId = null;
        for (elements, 0..) |element_ty, position| {
            const index = try self.store.append(.{ .scalar = .{ .u64 = @intCast(position) } });
            const element_meta = try self.metaNode(try self.tyNode(element_ty, region), region);
            const left = try self.tag("Index", &.{ lhs, index, element_meta });
            const right = try self.tag("Index", &.{ rhs, index, element_meta });
            const compare = try self.structuralEqOver(left, right, element_ty, bool_meta, region);
            conjunction = try self.andNode(conjunction, compare, bool_meta);
        }
        return conjunction orelse self.trueNode(bool_meta);
    }

    fn andNode(
        self: *Reifier,
        left: ?ConstNodeId,
        right: ConstNodeId,
        bool_meta: ConstNodeId,
    ) Allocator.Error!ConstNodeId {
        const first = left orelse return right;
        return self.tag("Binop", &.{ try self.strNode("and"), first, right, bool_meta });
    }

    fn trueNode(self: *Reifier, bool_meta: ConstNodeId) Allocator.Error!ConstNodeId {
        return self.boolLiteralNode(true, bool_meta);
    }

    fn boolLiteralNode(self: *Reifier, flag: bool, bool_meta: ConstNodeId) Allocator.Error!ConstNodeId {
        const lit = try self.tag("Bool", &.{try self.tag(if (flag) "True" else "False", &.{})});
        return self.tag("Lit", &.{ lit, bool_meta });
    }

    /// A derived `to_hash`. Threading composes by return value, so the whole
    /// recipe is a nest of calls needing no binder: each component feeds the
    /// hasher the one before it produced.
    ///
    /// The reifier expands it rather than leaving it to the stage because a
    /// hash has to agree with the Roc side feeding the same keys, and component
    /// order, traversal order and write widths are the compiler's to decide.
    /// Where the walk cannot reach, the node stays a `Derived` and the stage
    /// has to refuse it: nothing else can reproduce those three.
    fn structuralHashNode(
        self: *Reifier,
        value_id: CheckedExprId,
        hasher_id: CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const value_ty = self.bodies.expr(value_id).ty;
        const hasher_ty = self.bodies.expr(hasher_id).ty;
        const value = try self.irNode(value_id);
        const hasher = try self.irNode(hasher_id);
        const writer = self.typeName(hasher_ty) orelse
            return self.reject(.unresolved_type, region, "the hasher this derivation threads");

        if (try self.structuralHashOver(value, hasher, value_ty, writer, meta, region)) |hashed| {
            return hashed;
        }
        return self.derivedNode("to_hash", value_ty, &.{ value, hasher }, meta, region);
    }

    /// Feed `value` into `acc`, one component at a time, left to right. `null`
    /// means the walk met something it cannot describe, which is the caller's
    /// signal to leave the whole derivation symbolic rather than describe part
    /// of it.
    fn structuralHashOver(
        self: *Reifier,
        value: ConstNodeId,
        acc: ConstNodeId,
        type_id: CheckedTypeId,
        writer: []const u8,
        hasher_meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        switch (self.types.payload(type_id)) {
            .alias => |alias| return self.structuralHashOver(value, acc, alias.backing, writer, hasher_meta, region),
            .nominal => |nominal| {
                if (nominal.builtin) |builtin_nominal| {
                    const width = hasherWriteName(builtin_nominal) orelse return null;
                    const callee = try std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ writer, width });
                    defer self.gpa.free(callee);
                    const args = try self.store.append(.{ .list = .{ .nodes = &.{ acc, value } } });
                    return try self.tag("Call", &.{ try self.strNode(callee), args, hasher_meta });
                }
                switch (try self.nominalMethod("to_hash", nominal, type_id, &.{ value, acc }, hasher_meta, region)) {
                    .written => |call| return call,
                    .derived => {},
                    .undeclared => return null,
                }
                if (nominal.is_opaque) return null;
                const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse return null;
                return self.structuralHashOver(value, acc, backing, writer, hasher_meta, region);
            },
            .record => |record| return self.fieldsHashOver(value, acc, record.fields, writer, hasher_meta, region),
            .tuple => |elements| return self.elementsHashOver(value, acc, elements, writer, hasher_meta, region),
            // Nothing to feed the hasher, so the accumulator passes through.
            .empty_record => return acc,
            .flex, .rigid, .pending, .err, .function, .tag_union, .empty_tag_union => return null,
        }
    }

    fn fieldsHashOver(
        self: *Reifier,
        value: ConstNodeId,
        acc: ConstNodeId,
        fields: []const checked.CheckedRecordField,
        writer: []const u8,
        hasher_meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        var threaded = acc;
        for (fields) |field| {
            const name = try self.strNode(self.names.recordFieldLabelText(field.name));
            const field_meta = try self.metaNode(try self.tyNode(field.ty, region), region);
            const component = try self.tag("Field", &.{ value, name, field_meta });
            threaded = try self.structuralHashOver(component, threaded, field.ty, writer, hasher_meta, region) orelse
                return null;
        }
        return threaded;
    }

    fn elementsHashOver(
        self: *Reifier,
        value: ConstNodeId,
        acc: ConstNodeId,
        elements: []const CheckedTypeId,
        writer: []const u8,
        hasher_meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        var threaded = acc;
        for (elements, 0..) |element_ty, position| {
            const index = try self.store.append(.{ .scalar = .{ .u64 = @intCast(position) } });
            const element_meta = try self.metaNode(try self.tyNode(element_ty, region), region);
            const component = try self.tag("Index", &.{ value, index, element_meta });
            threaded = try self.structuralHashOver(component, threaded, element_ty, writer, hasher_meta, region) orelse
                return null;
        }
        return threaded;
    }

    /// A compiler-derived method, left for the stage to expand. The recipe is
    /// fixed by the type rather than written in Roc, so there is no body to
    /// walk.
    ///
    /// The subject type is a field of its own because the operands do not carry
    /// it. `Row.parser_for(encoding)` names `Row` only in the plan's
    /// dispatcher, and the node's own type is the parser it constructs, so a
    /// stage would otherwise reach `Row` by digging through the codec
    /// protocol's shape.
    fn derivedNode(
        self: *Reifier,
        method: []const u8,
        subject_ty: CheckedTypeId,
        args: []const ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const subject = try self.tyNode(subject_ty, region);
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return self.tag("Derived", &.{ try self.strNode(method), subject, list, meta });
    }

    /// One node for a derived codec that was constructed and then run.
    ///
    /// `parser_for` and `encoder_for` hand back the codec rather than running
    /// it, so a body always constructs one and applies the result. Applying a
    /// function value has no node, and giving the `Ir` one would make every
    /// translator carry a case it cannot emit, so the two halves fold: the
    /// constructor's arguments come first, the applied ones after, and the
    /// binding the constructor was held in leaves nothing behind.
    ///
    /// Null when the callee is not a held or freshly constructed codec, which
    /// is every other call.
    fn foldedCodecNode(
        self: *Reifier,
        func: CheckedExprId,
        operands: []const CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        const plan_id = self.codecCallee(func) orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const constructed = plan.argsSlice(self.plans);

        const args = try self.gpa.alloc(ConstNodeId, constructed.len + operands.len);
        defer self.gpa.free(args);
        for (constructed, 0..) |operand, index| {
            args[index] = switch (operand) {
                .checked_expr => |child| try self.irNode(child),
                .generated_numeral, .generated_quote, .generated_interpolation_segments => return self.rejectError(
                    .unsupported_expression,
                    region,
                    "a compiler-generated argument",
                ),
            };
        }
        for (operands, 0..) |child, index| args[constructed.len + index] = try self.irNode(child);

        return try self.derivedNode(
            self.names.methodNameText(plan.method),
            plan.dispatcher_ty,
            args,
            meta,
            region,
        );
    }

    /// The derived codec a call's callee is: one a binding holds, or one the
    /// callee constructs on the spot in `Shape.encoder_for(fmt)(value, state)`.
    fn codecCallee(self: *Reifier, func: CheckedExprId) ?static_dispatch.StaticDispatchPlanId {
        const callee = self.bodies.expr(func);
        if (callee.data == .lookup_local) {
            const binder = self.bodies.patternBinderForCheckedPattern(callee.data.lookup_local.pattern) orelse
                return null;
            const binding = self.lookupBinding(binder) orelse return null;
            return switch (binding.kind) {
                .function => |bound| self.derivedCodecPlan(bound),
                .param, .local, .constant, .callee => null,
            };
        }
        return self.derivedCodecPlan(func);
    }

    /// The plan behind a derived parser or encoder construction, when the
    /// expression is one.
    ///
    /// Both spellings reach the same plan: `Shape.encoder_for` dispatches on a
    /// type and `value.encoder_for` on a value, and a constrained body reaches
    /// it through the evidence its caller supplied.
    fn derivedCodecPlan(self: *Reifier, expr_id: CheckedExprId) ?static_dispatch.StaticDispatchPlanId {
        const dispatched = switch (self.bodies.expr(expr_id).data) {
            .dispatch_call, .type_dispatch_call => |plan_id| plan_id,
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return null,
        };
        const plan_id = dispatched orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const derivation = switch (plan.resolution) {
            .structural => |structural| structural,
            .evidence_dependent => |forwarded| self.forwardedDerivation(forwarded.index) orelse return null,
            .direct_pending,
            .direct_closed,
            .direct_parametric,
            .checked_error,
            .@"unreachable",
            => return null,
        };
        return switch (derivation) {
            .parser, .encoder => plan_id,
            // Equality and hashing run where they are written, and a derived
            // `map` takes its function as an argument, so none of the three is
            // curried and none needs folding.
            .equality, .hash, .map, .map_effectful => null,
        };
    }

    /// Whether an expression is a call that hands back a function.
    ///
    /// The block holds one of these rather than binding it, because a function
    /// value has no `Ir` node of its own and the call that runs it folds both
    /// halves into one. A binding the call never runs describes nowhere, which
    /// is the refusal a reference to it already reports.
    fn constructsFunction(self: *Reifier, expr_id: CheckedExprId) bool {
        const expr = self.bodies.expr(expr_id);
        const calls = switch (expr.data) {
            .call, .dispatch_call, .type_dispatch_call => true,
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => false,
        };
        return calls and self.functionOf(expr.ty) != null;
    }

    /// The lambda an expression is, looking through a closure, or null when it
    /// is not one.
    fn lambdaOf(self: *Reifier, expr_id: CheckedExprId) ?LambdaData {
        const data = self.bodies.expr(expr_id).data;
        if (data == .lambda) return data.lambda;
        if (data != .closure) return null;
        const wrapped = self.bodies.expr(data.closure.lambda).data;
        if (wrapped != .lambda) return null;
        return wrapped.lambda;
    }

    /// Whether a definition hands back a function rather than a value: its
    /// body is a lambda whose body is another lambda.
    ///
    /// A body that merely evaluates to a lambda, through a block or an `if`,
    /// is not one of these: the shape has to be there to be flattened.
    fn isCurried(self: *Reifier, body: CheckedExprId) bool {
        const outer = self.lambdaOf(body) orelse return false;
        return self.lambdaOf(outer.body) != null;
    }

    /// The call one expression constructed a function with: the call itself,
    /// or the one a held binding remembers.
    fn constructorCall(self: *Reifier, func: CheckedExprId) ?CheckedExprId {
        const callee = self.bodies.expr(func);
        if (callee.data != .lookup_local) {
            return if (self.constructsFunction(func)) func else null;
        }
        const binder = self.bodies.patternBinderForCheckedPattern(callee.data.lookup_local.pattern) orelse
            return null;
        const binding = self.lookupBinding(binder) orelse return null;
        return switch (binding.kind) {
            .function => |bound| bound,
            .param, .local, .constant, .callee => null,
        };
    }

    /// One `Call` for a definition that hands back a function and a use that
    /// runs it.
    ///
    /// `Ir` has no node for applying an expression, and a translator emitting
    /// GLSL or SQL has nowhere to put a function value, so the two halves
    /// resolve here instead: the row gathers both lambdas' parameters, the
    /// constructor's arguments come first and the applied ones after, and the
    /// site writes one `Call`.
    ///
    /// Null when the callee is not a curried definition, which is every other
    /// call.
    fn curriedCallNode(
        self: *Reifier,
        func: CheckedExprId,
        operands: []const CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        const constructor = self.constructorCall(func) orelse return null;
        const built = self.bodies.expr(constructor).data;
        if (built == .call) {
            const call = built.call;
            const resolved = try self.calleeTarget(call.func, region);
            if (resolved != .definition) return null;
            var callee = resolved.definition;
            errdefer if (callee.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
            if (self.plans.siteEvidence(call.func)) |supplied| {
                callee.evidence = .{ .reader = self, .entries = supplied };
            }
            return self.flattenedCallNode(callee, call.args, operands, meta, region);
        }

        const id = switch (built) {
            .dispatch_call, .type_dispatch_call => |plan_id| plan_id orelse return null,
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return null,
        };
        const plan = self.plans.plans[@backingInt(id)];
        const spelled = try self.calleeName(plan, self.names.methodNameText(plan.method));
        defer self.gpa.free(spelled);
        // A method the walk cannot reach a body for has no row to flatten, so
        // the call describes the way it did before: as the refusal a call to a
        // function value has always been.
        const found = self.dispatchTarget(plan, spelled, region) catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.Rejected => return null,
        };
        var callee = switch (found) {
            .definition => |target| target,
            // A builtin carries no body to flatten a curried call through.
            .provided, .spelled => return null,
        };
        errdefer if (callee.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
        const constructed = try self.dispatchExprs(plan, region);
        defer self.gpa.free(constructed);
        return self.flattenedCallNode(callee, constructed, operands, meta, region);
    }

    /// One `Call` over both argument groups, against the row that gathers both
    /// lambdas' parameters.
    ///
    /// Takes the callee's instantiation either way: a callee that turns out
    /// not to be curried is released here and the call describes as the
    /// refusal it was.
    fn flattenedCallNode(
        self: *Reifier,
        callee: CalleeTarget,
        constructed: []const CheckedExprId,
        operands: []const CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!?ConstNodeId {
        var target = callee;
        if (!target.reader.isCurried(target.key.body)) {
            if (target.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
            return null;
        }
        target.key.curried = true;

        const captures = target.captures;
        const name = try self.calledDefinition(.{ .definition = target }, region);
        const args = try self.callArgs(captures, &.{ constructed, operands });
        defer self.gpa.free(args);
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return try self.tag("Call", &.{ try self.strNode(name), list, meta });
    }

    /// One dispatch's operands as checked expressions. The caller owns the
    /// slice.
    fn dispatchExprs(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        region: base.Region,
    ) Error![]CheckedExprId {
        const operands = plan.argsSlice(self.plans);
        const exprs = try self.gpa.alloc(CheckedExprId, operands.len);
        errdefer self.gpa.free(exprs);
        for (operands, 0..) |operand, index| {
            exprs[index] = switch (operand) {
                .checked_expr => |child| child,
                .generated_numeral, .generated_quote, .generated_interpolation_segments => return self.rejectError(
                    .unsupported_expression,
                    region,
                    "a compiler-generated argument",
                ),
            };
        }
        return exprs;
    }

    /// A plain call to a named function, `f(x)`, carried as the same `Call` a
    /// static dispatch produces.
    ///
    /// The description names the callee and stops there rather than inlining
    /// the body behind it, so a translator keeps the structure the author
    /// wrote and resolves each name against the descriptions it holds.
    fn callNode(
        self: *Reifier,
        func: CheckedExprId,
        operands: []const CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // `Str.inspect` has no body to name, because the compiler writes the
        // rendering, so it is recognised by the intrinsic the checker recorded
        // for this use rather than resolved as a callee.
        if (self.calleeIntrinsic(func)) |intrinsic| {
            if (intrinsic == .str_inspect and operands.len == 1) return self.inspectNode(operands[0], meta, region);
        }
        if (try self.foldedCodecNode(func, operands, meta, region)) |folded| return folded;
        if (try self.curriedCallNode(func, operands, meta, region)) |flattened| return flattened;
        var callee = try self.calleeTarget(func, region);
        // Arity is the operator's, not the callee's: a builtin the `Ir` folds
        // into a `Unary` takes the one operand that node holds.
        if (callee == .unary and operands.len == 1) {
            const inner = try self.irNode(operands[0]);
            return self.tag("Unary", &.{ try self.strNode(callee.unary), inner, meta });
        }
        // The callee reference is the instantiation edge the checker keyed its
        // evidence by, so the answer to every `where` obligation of the callee
        // is in hand here and nowhere inside the body.
        if (callee == .definition) {
            if (self.plans.siteEvidence(func)) |supplied| {
                callee.definition.evidence = .{ .reader = self, .entries = supplied };
            }
        }
        // A function argument has no node, so the site that fixes it resolves
        // it: the parameter binds to the definition the argument names, the
        // row is keyed by that as well as by the types, and neither the
        // signature nor the call carries the parameter.
        if (callee == .definition) {
            try self.bindCallees(&callee.definition, operands, region);
        }
        const captures = switch (callee) {
            .definition => |definition| definition.captures,
            .provided, .unary => &.{},
        };
        const bound = switch (callee) {
            .definition => |definition| definition.bound,
            .provided, .unary => &.{},
        };
        // The kept operands are gathered before the callee is described,
        // because describing it is what frees what the call bound.
        const kept = try self.keptOperands(operands, bound);
        defer self.gpa.free(kept);
        const name = try self.calledDefinition(callee, region);
        const args = try self.callArgs(captures, &.{kept});
        defer self.gpa.free(args);
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return self.tag("Call", &.{ try self.strNode(name), list, meta });
    }

    /// Resolve every function argument this call passes to the definition it
    /// names, and key the callee's row by them.
    ///
    /// A function chosen by an `if`, read out of a record or taken from a list
    /// names no definition, so it stays the refusal it has always been. So
    /// does one that captures: the row is described on its own, and a capture
    /// of the caller's scope has nothing to read inside the callee.
    fn bindCallees(
        self: *Reifier,
        target: *CalleeTarget,
        operands: []const CheckedExprId,
        region: base.Region,
    ) Error!void {
        var bound = std.ArrayList(BoundCallee).empty;
        errdefer {
            self.releaseBound(bound.items);
            bound.deinit(self.gpa);
        }
        for (operands, 0..) |operand, index| {
            if (self.functionOf(self.bodies.expr(operand).ty) == null) continue;
            const passed = try self.passedCallee(operand, region);
            try bound.append(self.gpa, .{ .param = @intCast(index), .target = passed });
        }
        if (bound.items.len == 0) return;
        target.key.callees = boundCalleesKey(bound.items);
        target.bound = try bound.toOwnedSlice(self.gpa);
    }

    /// The definition one function argument names: a name the caller wrote, or
    /// the row a lambda written at the site lifts into.
    fn passedCallee(self: *Reifier, operand: CheckedExprId, region: base.Region) Error!CalleeTarget {
        if (self.lambdaOf(operand) != null) {
            if (self.capturesOf(operand).len != 0) {
                return self.rejectError(.capture, region, self.capturedName(self.capturesOf(operand)[0].pattern));
            }
            return .{
                .key = .{ .artifact = self.artifact.bytes, .body = operand },
                .spelling = try self.lambdaArgumentSpelling(operand, region),
                .reader = self,
                .lifted = true,
            };
        }
        const resolved = try self.calleeTarget(operand, region);
        return switch (resolved) {
            .definition => |definition| definition,
            .provided, .unary => self.rejectError(.unsupported_expression, region, "a function the compiler provides, passed as an argument"),
        };
    }

    /// What a lambda written at a call site is named after: the first name
    /// its parameters bind, because the lambda itself binds no name. One whose
    /// parameters bind no name at all, `|_| ..`, is named `lambda`.
    fn lambdaArgumentSpelling(
        self: *Reifier,
        operand: CheckedExprId,
        region: base.Region,
    ) Error!CalleeSpelling {
        const lambda = try self.lambdaData(operand);
        if (lambda.args.len == 0) {
            return self.rejectError(.unsupported_expression, region, "a lambda that takes no argument");
        }
        for (lambda.args) |arg| {
            if (self.firstBinder(arg)) |binder| return .{ .binder = binder };
        }
        const spelled = try std.fmt.allocPrint(self.gpa, "{s}.lambda", .{self.env.module_name});
        errdefer self.gpa.free(spelled);
        try self.invented_names.append(self.gpa, spelled);
        return .{ .written = spelled };
    }

    /// The first name a pattern binds, reading it left to right.
    fn firstBinder(self: *Reifier, pattern_id: CheckedPatternId) ?checked.PatternBinderId {
        return switch (self.bodies.pattern(pattern_id).data) {
            .assign => |binder| binder,
            .as => |renamed| renamed.binder,
            .tuple => |items| for (items) |item| {
                if (self.firstBinder(item)) |binder| break binder;
            } else null,
            .record_destructure => |destructs| for (destructs) |destruct| {
                const inner = switch (destruct.kind) {
                    .required, .sub_pattern, .rest => |inner| inner,
                };
                if (self.firstBinder(inner)) |binder| break binder;
            } else null,
            .pending,
            .applied_tag,
            .nominal,
            .list,
            .numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => null,
        };
    }

    /// Which definitions a call fixed a callee's function parameters to,
    /// digested so two calls at one set of definitions share a row and two at
    /// different ones take one each.
    fn boundCalleesKey(bound: []const BoundCallee) [32]u8 {
        var hasher = std.crypto.hash.Blake3.init(.{});
        for (bound) |entry| {
            hasher.update(std.mem.asBytes(&entry.param));
            hasher.update(&entry.target.key.artifact);
            hasher.update(std.mem.asBytes(&entry.target.key.body));
            hasher.update(&entry.target.key.instantiation);
            hasher.update(&entry.target.key.callees);
        }
        var key: [32]u8 = undefined;
        hasher.final(&key);
        return key;
    }

    /// Release what a call resolved for its callee's function parameters.
    fn releaseBound(self: *Reifier, bound: []BoundCallee) void {
        for (bound) |*entry| {
            if (entry.target.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
            self.releaseBound(entry.target.bound);
        }
        self.gpa.free(bound);
    }

    /// The arguments one call still passes, leaving out every one that fixed a
    /// function parameter: those name definitions the row already resolved.
    /// The caller owns the slice.
    fn keptOperands(
        self: *Reifier,
        operands: []const CheckedExprId,
        bound: []const BoundCallee,
    ) Allocator.Error![]CheckedExprId {
        const kept = try self.gpa.alloc(CheckedExprId, operands.len - bound.len);
        errdefer self.gpa.free(kept);
        var next: usize = 0;
        for (operands, 0..) |operand, index| {
            if (fixesCallee(bound, index)) continue;
            kept[next] = operand;
            next += 1;
        }
        return kept;
    }

    /// Whether one argument position fixed a function parameter.
    fn fixesCallee(bound: []const BoundCallee, index: usize) bool {
        for (bound) |entry| {
            if (entry.param == index) return true;
        }
        return false;
    }

    /// The nodes one call passes: what a lifted callee captured, in the order
    /// its row takes them, then the arguments the site wrote.
    ///
    /// A capture is lexical, so every call to one lifted lambda sits in the
    /// scope that holds what it captured, and the node reads the same at each
    /// site. The caller owns the slice.
    fn callArgs(
        self: *Reifier,
        captures: []const checked.CheckedCapture,
        groups: []const []const CheckedExprId,
    ) Error![]ConstNodeId {
        var total = captures.len;
        for (groups) |group| total += group.len;
        const args = try self.gpa.alloc(ConstNodeId, total);
        errdefer self.gpa.free(args);

        for (captures, 0..) |capture, index| {
            const pattern = self.bodies.pattern(capture.pattern);
            const ty = try self.tyNode(pattern.ty, pattern.source_region);
            const meta = try self.metaNode(ty, pattern.source_region);
            args[index] = try self.lookupNode(capture.pattern, null, meta, pattern.source_region);
        }
        var next = captures.len;
        for (groups) |group| {
            for (group) |child| {
                args[next] = try self.irNode(child);
                next += 1;
            }
        }
        return args;
    }

    /// The name a plain call names its callee by, with the callee described
    /// into the site's table if the walk has not met it already.
    ///
    /// The description names the callee and stops there rather than writing
    /// the callee's body into it, so the structure the author wrote survives
    /// into the target and a recursive function describes at all. The body
    /// goes into the table beside the root, which is what the name resolves
    /// against.
    fn calledDefinition(self: *Reifier, callee: Callee, region: base.Region) Error![]const u8 {
        var target = switch (callee) {
            .definition => |definition| definition,
            // A function the compiler provides is named and nothing else: the
            // name is the whole description, so no row is written and none is
            // recorded against the frame.
            .provided => |name| return name,
            .unary => return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides"),
        };
        // The walk of the callee's body borrows the substitution and the
        // bound callees, and that walk finishes here, so the call that read
        // them also frees them.
        defer if (target.instantiation) |*instance| instance.substitution.deinit(self.gpa);
        defer self.releaseBound(target.bound);
        try self.recordCallee(target.key);

        if (self.walk.definitions.getPtr(target.key)) |existing| {
            if (existing.name) |name| return name;
            // The site's own root carries no name until a call reaches it,
            // because a description names the root nowhere else.
            const name = try self.calleeRowName(target);
            existing.name = name;
            return name;
        }

        const name = try self.calleeRowName(target);
        _ = try target.reader.describeDefinition(target.key, name, target.instantiation, target.evidence, target.bound, target.at);
        return self.walk.definitions.get(target.key).?.name.?;
    }

    /// The row name one callee takes: the name the author wrote, unless a row
    /// already answers to it.
    ///
    /// One name can stand for more than one row. A generic definition takes
    /// one row per instantiation, a call fixing a function parameter takes one
    /// per set of callees, a flattened row is a second shape of one
    /// definition, and two blocks can each lift a lambda of the same name. So
    /// the walk counts rows per spelling and every row after the first takes
    /// its count as a serial, which is what tells it from the rows before it.
    ///
    /// The count is what decides, rather than a property of the row, because
    /// the properties over-name: an annotated `-> Try(a, [Tag])` is generic in
    /// its error row, so a conversion a program calls once would carry a
    /// serial that distinguishes it from nothing. A type mangle would name a
    /// row too, but a record's is unbounded, and a translator reads the
    /// instantiation off the row's own type rather than out of its name.
    fn calleeRowName(self: *Reifier, target: CalleeTarget) Allocator.Error![]u8 {
        const spelling = switch (target.spelling) {
            .binder => |binder| try target.reader.qualifiedName(binder),
            .written => |written| try self.gpa.dupe(u8, written),
        };
        const serial = try self.walk.nameSerial(spelling);
        if (serial == 0) return spelling;
        defer self.gpa.free(spelling);
        return std.fmt.allocPrint(self.gpa, "{s}#{d}", .{ spelling, serial });
    }

    /// `Module.name`, the key a `Call` names a definition by. Read on the
    /// reader of the module that defines it, because both halves are that
    /// module's.
    ///
    /// Qualified because one table holds the definitions of every module a
    /// description reaches, and a key has to be unique across it.
    fn qualifiedName(self: *Reifier, binder: checked.PatternBinderId) Allocator.Error![]u8 {
        return std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ self.env.module_name, self.binderName(binder) });
    }

    /// The definition a plain call's callee names, or a refusal naming why the
    /// callee is not one.
    ///
    /// The lookup form says where the name was written; the resolved reference
    /// says what it reached. So a `lookup_local` the staged scope holds is a
    /// parameter or a binding and is refused here, and everything else is
    /// decided by the reference.
    fn calleeTarget(self: *Reifier, func: CheckedExprId, region: base.Region) Error!Callee {
        const callee = self.bodies.expr(func);
        if (callee.data == .lookup_local) {
            const local = callee.data.lookup_local;
            const binder = self.bodies.patternBinderForCheckedPattern(local.pattern) orelse
                return self.rejectError(.unresolved_reference, region, "this call");
            if (self.lookupBinding(binder)) |binding| return self.liftedTarget(binding, binder, callee.ty, region);
            if (try self.replayBinding(binder)) |binding| return self.liftedTarget(binding, binder, callee.ty, region);
            const resolved = local.resolved orelse
                return self.rejectError(.unresolved_reference, region, "this call");
            return self.resolvedTarget(resolved, binder, region);
        }
        const resolved = switch (callee.data) {
            .lookup_external, .lookup_required => |reference| reference orelse
                return self.rejectError(.unresolved_reference, region, "this call"),
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return self.rejectError(.unsupported_expression, region, "a call to a function value"),
        };
        return self.resolvedTarget(resolved, null, region);
    }

    /// A lambda the staged body bound, lifted into a row of its own.
    ///
    /// The `Ir` is first order, so a helper written inside the function that
    /// uses it is a definition like any other: the call names it and the body
    /// goes in the table beside every other row. Two functions can each write
    /// one called `step`, so the row takes a serial.
    ///
    /// Every other held name is a function with no lambda behind it, which is
    /// the refusal a call to a function value has always been.
    ///
    /// A lambda the block generalized describes at the type `use`, the type
    /// the call's lookup instantiated its scheme to, so each type it is called
    /// at keys a row of its own.
    fn liftedTarget(
        self: *Reifier,
        binding: Binding,
        binder: checked.PatternBinderId,
        use: CheckedTypeId,
        region: base.Region,
    ) Error!Callee {
        const bound = switch (binding.kind) {
            .function => |expr_id| expr_id,
            // The call fixed this parameter to a definition, so the name it
            // resolves to is that definition's and the row is already keyed
            // by it. The substitution is copied because the walk of this body
            // frees what it reads, and the call that bound it frees its own.
            .callee => |index| return .{ .definition = try self.boundTarget(self.bound[index].target) },
            .param, .local, .constant => return self.rejectError(.unsupported_expression, region, "a call to a function value"),
        };
        if (self.lambdaOf(bound) == null) {
            return self.rejectError(.unsupported_expression, region, "a call to a function value");
        }
        var instance = if (self.localScheme(bound)) |scheme|
            try self.instantiationOf(scheme, self, use, region, .call)
        else
            null;
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        return .{ .definition = .{
            .key = .{
                .artifact = self.artifact.bytes,
                .body = bound,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .spelling = .{ .binder = binder },
            .reader = self,
            .instantiation = instance,
            .lifted = true,
            .captures = self.capturesOf(bound),
        } };
    }

    /// One bound callee, copied for the call that names it.
    ///
    /// Everything but the substitution and the nested bindings is borrowed:
    /// those two are owned, and one call's ownership cannot be another's.
    fn boundTarget(self: *Reifier, target: CalleeTarget) Error!CalleeTarget {
        var copy = target;
        if (target.instantiation) |fixed| {
            copy.instantiation = .{
                .substitution = try fixed.substitution.clone(self.gpa),
                .key = fixed.key,
            };
        }
        errdefer if (copy.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
        copy.bound = try self.gpa.alloc(BoundCallee, target.bound.len);
        for (target.bound, 0..) |entry, index| {
            copy.bound[index] = .{ .param = entry.param, .target = try self.boundTarget(entry.target) };
        }
        return copy;
    }

    /// The definition a resolved reference reaches, and the reader that walks
    /// it.
    ///
    /// Every hop is a ref the producer recorded: the reference names a
    /// binding, the binding names a template, and the template holds the body.
    /// That chain is the one that survives publication, because a module's
    /// source-node map is build-only and a module read back from cache has
    /// none.
    ///
    /// `written_binder` is what the call site's own name binds, which names a
    /// definition of this module. An imported binding carries a pattern of its
    /// own instead, so the name is read in the module that defines it.
    fn resolvedTarget(
        self: *Reifier,
        resolved: checked.ResolvedValueRefId,
        written_binder: ?checked.PatternBinderId,
        region: base.Region,
    ) Error!Callee {
        const use = switch (self.value_refs.callableTarget(resolved).ref) {
            // A promoted local function is a procedure of the module with a
            // binding of its own, which captures nothing: the checker proved
            // it self-contained, so the walk reads it as a top-level one.
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| use,
            .hosted_proc => return self.rejectError(.unsupported_expression, region, "a call to a function the host provides"),
            .local_proc => return self.rejectError(.unsupported_expression, region, "a call to a function defined inside another function"),
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .selected_hoisted_const,
            .top_level_const,
            .imported_const,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            => return self.rejectError(.unsupported_expression, region, "a call to a function value"),
        };
        return switch (use.binding) {
            .top_level => |top_level| self.hereTarget(top_level, written_binder, use, region),
            .imported => |imported| self.awayTarget(imported, use, region),
            .hosted => self.rejectError(.unsupported_expression, region, "a call to a function the host provides"),
            .platform_required => self.rejectError(.unsupported_expression, region, "a call to a function the platform requires"),
        };
    }

    /// A definition of the module being walked.
    fn hereTarget(
        self: *Reifier,
        binding_ref: checked.ArtifactTopLevelProcedureBindingRef,
        written_binder: ?checked.PatternBinderId,
        use: checked.ProcedureUseTemplate,
        region: base.Region,
    ) Error!Callee {
        if (!std.meta.eql(binding_ref.artifact.bytes, self.artifact.bytes)) {
            return self.rejectError(.unresolved_reference, region, "this call");
        }
        const binder = written_binder orelse
            return self.rejectError(.unresolved_reference, region, "this call");
        const template_ref = switch (self.procedure_bindings.get(binding_ref.binding).body) {
            .direct_template => |direct| switch (direct.template) {
                .checked => |template| template,
                .lifted, .synthetic => return self.rejectError(.unresolved_reference, region, "this call"),
            },
            .callable_eval_template, .checked_error => return self.rejectError(.unresolved_reference, region, "this call"),
        };
        const templates = self.procedure_templates.templates.items;
        const raw = @backingInt(template_ref.template);
        if (raw >= templates.len) return self.rejectError(.unresolved_reference, region, "this call");
        const template = templates[raw];
        const body = switch (template.body) {
            .checked_body => |body_id| self.bodies.body(body_id).root_expr,
            .intrinsic_wrapper, .entry_wrapper, .unimplemented => return self.rejectError(.unresolved_reference, region, "this call"),
        };
        var instance = try self.instantiationOf(self.templateScheme(template), self, use.source_fn_ty_payload, region, .call);
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        return .{ .definition = .{
            .key = .{
                .artifact = self.artifact.bytes,
                .body = body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .spelling = .{ .binder = binder },
            .reader = self,
            .instantiation = instance,
        } };
    }

    /// A definition of a module this one reaches through an import.
    ///
    /// The binding ref names the artifact, the definition and the pattern the
    /// definition binds, so the name and the body both come from the module
    /// that owns them.
    fn awayTarget(
        self: *Reifier,
        binding_ref: checked.ImportedProcedureBindingRef,
        use: checked.ProcedureUseTemplate,
        region: base.Region,
    ) Error!Callee {
        const definition = self.walk.foreign.findExported(binding_ref.artifact, binding_ref.def) orelse
            return self.rejectError(.unsupported_expression, region, "a call to a function in a module this one does not read");
        // The walk stops where the user's program does. A builtin's body is
        // the compiler's, and the `Ir` already has a node for most of what one
        // does, so writing `Bool.not`'s `match` into the table would hand a
        // translator a worse description than the `Unary` it handles. One the
        // `Ir` does have a node for folds into it; the rest is named and
        // nothing more, and a translator resolves the name against what its
        // own target provides.
        if (definition.module.env.module_role == .builtin) {
            const names = definition.module.sources.names;
            if (providedName(definition)) |export_name| {
                if (self.walk.builtinOperators(names).unaryOp(export_name.id)) |op| return .{ .unary = op };
                return .{ .provided = export_name.text };
            }
            return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides");
        }
        const reader = try self.walk.reader(definition.module);
        const binder = reader.bodies.patternBinderForCheckedPattern(binding_ref.pattern) orelse
            return reader.rejectError(.unresolved_reference, region, "this call");
        var instance = try reader.instantiationOf(reader.templateScheme(definition.template), self, use.source_fn_ty_payload, region, .call);
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        return .{ .definition = .{
            .key = .{
                .artifact = binding_ref.artifact.bytes,
                .body = definition.body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .spelling = .{ .binder = binder },
            .reader = reader,
            .instantiation = instance,
        } };
    }

    /// The name a function the compiler provides answers to, and the id the
    /// operator table is keyed by.
    const ProvidedName = struct {
        id: canonical.ExportNameId,
        text: []const u8,
    };

    /// What a builtin is called in a description: its export name.
    ///
    /// That name is the one spelling the compiler already holds for every
    /// builtin procedure, and it is unique across the builtin module, so a
    /// plain call and a method call on the same builtin land on it alike and
    /// a translator resolves one name rather than two. A procedure the
    /// builtin module does not export has none, and the site refuses.
    fn providedName(definition: ForeignDefinition) ?ProvidedName {
        const names = definition.module.sources.names;
        const proc_base = names.procBase(definition.template.proc_base);
        const id = proc_base.export_name orelse return null;
        return .{ .id = id, .text = names.exportNameText(id) };
    }

    /// What one use fixes a generic definition's quantified variables to, or
    /// null when the definition has none.
    ///
    /// `self` reads the definition's template and `caller` reads the use,
    /// because a definition in another module names its types in its own store
    /// and the type the use fixes it to is named in the caller's.
    ///
    /// `fixed` is that type: the payload a call carries for its callee, or the
    /// `f` of the `Code(f)` a site stands at. The two are the same question,
    /// so a generic root describes at the type its site fixed it to the way a
    /// generic callee describes at the type its call fixed it to.
    fn instantiationOf(
        self: *Reifier,
        scheme: Scheme,
        caller: *Reifier,
        fixed: ?CheckedTypeId,
        region: base.Region,
        unfixed: Unfixed,
    ) Error!?Instantiation {
        const scheme_vars = scheme.vars;
        if (scheme_vars.len == 0) return null;
        const payload = fixed orelse
            return self.rejectError(.unresolved_type, region, unfixed.missing);

        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        try self.matchType(&substitution, scheme_vars, scheme.root, caller.resolvedType(payload));

        var rows = try self.rowVars(scheme.root);
        defer rows.deinit(self.gpa);

        // `scheme_vars` is the domain, so a variable the match left unbound is
        // a hole in the body, and a description with a hole in it is worse
        // than a report saying the use was not described. A row variable is
        // the exception, because no description names one.
        for (scheme_vars) |scheme_var| {
            if (substitution.contains(scheme_var)) continue;
            if (rows.contains(scheme_var)) continue;
            return self.rejectError(.unresolved_type, region, unfixed.partial);
        }
        return .{ .substitution = substitution, .key = instantiationKey(substitution, scheme_vars) };
    }

    /// The variables one scheme type stands a row on.
    ///
    /// `Ty` has no form for a row: a record describes as the fields it has and
    /// a tag union as the variants it has, and the variable standing for the
    /// rest is named nowhere. So a use that leaves one unfixed leaves no hole,
    /// and requiring it fixed would refuse every function returning an open
    /// tag union, which is every function returning a tag union at all.
    fn rowVars(self: *Reifier, scheme_id: CheckedTypeId) Allocator.Error!RowVars {
        var found: RowVars = .empty;
        errdefer found.deinit(self.gpa);
        var seen: RowVars = .empty;
        defer seen.deinit(self.gpa);
        try self.collectRowVars(&found, &seen, scheme_id);
        return found;
    }

    const RowVars = collections.DenseMapUnmanaged(CheckedTypeId, void);

    fn collectRowVars(self: *Reifier, found: *RowVars, seen: *RowVars, id: CheckedTypeId) Allocator.Error!void {
        if ((try seen.getOrPut(self.gpa, id)).found_existing) return;
        switch (self.types.payload(id)) {
            .alias => |alias| try self.collectRowVars(found, seen, alias.backing),
            .function => |fn_ty| {
                for (fn_ty.args) |arg| try self.collectRowVars(found, seen, arg);
                try self.collectRowVars(found, seen, fn_ty.ret);
            },
            // A nominal's backing is not descended, the way the walk does not
            // descend it: the args are what a use fixes.
            .nominal => |nominal| for (nominal.args) |arg| try self.collectRowVars(found, seen, arg),
            .tuple => |parts| for (parts) |part| try self.collectRowVars(found, seen, part),
            .record => |record| {
                for (record.fields) |field| try self.collectRowVars(found, seen, field.ty);
                try self.collectRowTail(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                for (union_ty.tags) |variant| {
                    for (variant.argsSlice(self.types)) |arg| try self.collectRowVars(found, seen, arg);
                }
                try self.collectRowTail(found, seen, union_ty.ext);
            },
            .empty_record, .empty_tag_union, .flex, .rigid, .pending, .err => {},
        }
    }

    /// Follow one extension chain to what it ends at, which is the row.
    fn collectRowTail(self: *Reifier, found: *RowVars, seen: *RowVars, id: CheckedTypeId) Allocator.Error!void {
        switch (self.types.payload(id)) {
            .alias => |alias| try self.collectRowTail(found, seen, alias.backing),
            .record => |record| {
                for (record.fields) |field| try self.collectRowVars(found, seen, field.ty);
                try self.collectRowTail(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                for (union_ty.tags) |variant| {
                    for (variant.argsSlice(self.types)) |arg| try self.collectRowVars(found, seen, arg);
                }
                try self.collectRowTail(found, seen, union_ty.ext);
            },
            .flex, .rigid => try found.put(self.gpa, id, {}),
            .function, .nominal, .tuple, .empty_record, .empty_tag_union, .pending, .err => {},
        }
    }

    /// The quantified variables of one template, in the scheme's own order.
    fn schemeVars(self: *Reifier, template: checked.CheckedProcedureTemplate) []const CheckedTypeId {
        const pool = self.procedure_templates.scheme_vars_pool;
        return pool[template.scheme_vars.start..][0..template.scheme_vars.len];
    }

    /// Read a scheme type and the type one call fixes it to together,
    /// recording what each quantified variable meets.
    ///
    /// Only a variable records anything, so a shape the two sides do not share
    /// stops the descent and leaves the variable it would have bound unbound,
    /// which `instantiationOf` reads as a refusal.
    ///
    /// The use side is resolved through the caller's own substitution at every
    /// step: a generic function calling a generic function writes the inner
    /// call in its own variables, and what the inner row is keyed by has to be
    /// the type the outer call fixed them to.
    fn matchType(
        self: *Reifier,
        substitution: *Substitution,
        scheme_vars: []const CheckedTypeId,
        scheme_id: CheckedTypeId,
        use: TypeRef,
    ) Allocator.Error!void {
        for (scheme_vars) |scheme_var| {
            if (scheme_var != scheme_id) continue;
            if (!substitution.contains(scheme_id)) try substitution.put(self.gpa, scheme_id, use);
            return;
        }
        switch (self.types.payload(scheme_id)) {
            .alias => |alias| try self.matchType(substitution, scheme_vars, alias.backing, use),
            .function => |scheme_fn| {
                const use_fn = use.reader.functionOf(use.id) orelse return;
                if (use_fn.args.len != scheme_fn.args.len) return;
                for (scheme_fn.args, use_fn.args) |arg, fixed| {
                    try self.matchType(substitution, scheme_vars, arg, use.reader.resolvedType(fixed));
                }
                try self.matchType(substitution, scheme_vars, scheme_fn.ret, use.reader.resolvedType(use_fn.ret));
            },
            .nominal => |scheme_nominal| {
                const use_nominal = use.reader.nominalOf(use.id) orelse return;
                if (use_nominal.args.len != scheme_nominal.args.len) return;
                for (scheme_nominal.args, use_nominal.args) |arg, fixed| {
                    try self.matchType(substitution, scheme_vars, arg, use.reader.resolvedType(fixed));
                }
            },
            .tuple => |scheme_elements| {
                const use_elements = use.reader.tupleOf(use.id) orelse return;
                if (use_elements.len != scheme_elements.len) return;
                for (scheme_elements, use_elements) |element, fixed| {
                    try self.matchType(substitution, scheme_vars, element, use.reader.resolvedType(fixed));
                }
            },
            .record => |scheme_record| try self.matchRecord(
                substitution,
                scheme_vars,
                scheme_record.fields,
                scheme_record.ext,
                use,
            ),
            .tag_union => |scheme_union| try self.matchTagUnion(
                substitution,
                scheme_vars,
                scheme_union.tags,
                scheme_union.ext,
                use,
            ),
            // A row variable is left unbound on purpose: `Ty` has no form for
            // a row, so a description of one would be a description of
            // something else.
            .empty_record,
            .empty_tag_union,
            .flex,
            .rigid,
            .pending,
            .err,
            => {},
        }
    }

    /// Pair a scheme record's fields with the use's by name, and match each
    /// pair. A field the use does not have leaves its variables unbound.
    fn matchRecord(
        self: *Reifier,
        substitution: *Substitution,
        scheme_vars: []const CheckedTypeId,
        fields: []const checked.CheckedRecordField,
        ext: ?CheckedTypeId,
        use: TypeRef,
    ) Allocator.Error!void {
        var scheme_fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer scheme_fields.deinit(self.gpa);
        try self.recordFields(&scheme_fields, fields, ext);

        var use_fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer use_fields.deinit(self.gpa);
        switch (use.reader.types.payload(use.id)) {
            .record => |use_record| try use.reader.recordFields(&use_fields, use_record.fields, use_record.ext),
            .alias,
            .empty_record,
            .tuple,
            .function,
            .nominal,
            .tag_union,
            .empty_tag_union,
            .flex,
            .rigid,
            .pending,
            .err,
            => return,
        }

        for (scheme_fields.items) |field| {
            for (use_fields.items) |fixed| {
                if (!self.sameFieldLabel(field.name, use.reader, fixed.name)) continue;
                try self.matchType(substitution, scheme_vars, field.ty, use.reader.resolvedType(fixed.ty));
                break;
            }
        }

        // The row the scheme stands on is the fields the use has beyond the
        // ones the scheme named, and `Ty.Record` is a closed list, so the walk
        // needs them. The use's whole record is what it binds to: the residual
        // is no type the artifact holds, and the walk drops a field a nearer
        // link already named.
        const row = self.recordRowTail(ext) orelse return;
        for (scheme_vars) |scheme_var| {
            if (scheme_var != row) continue;
            if (!substitution.contains(row)) try substitution.put(self.gpa, row, use);
            return;
        }
    }

    /// The variable one record type stands its row on, or null where its
    /// extension chain ends closed.
    fn recordRowTail(self: *Reifier, ext: ?CheckedTypeId) ?CheckedTypeId {
        var link = ext orelse return null;
        while (true) {
            switch (self.types.payload(link)) {
                .flex, .rigid => return link,
                .record => |record| link = record.ext,
                .alias => |alias| link = alias.backing,
                .pending,
                .err,
                .tuple,
                .nominal,
                .function,
                .empty_record,
                .tag_union,
                .empty_tag_union,
                => return null,
            }
        }
    }

    /// The fields a record type has, following its extension.
    ///
    /// Stops at anything that is not another record, because a match records
    /// what it reaches and `instantiationOf` refuses on what it did not.
    fn recordFields(
        self: *Reifier,
        into: *std.ArrayList(checked.CheckedRecordField),
        fields: []const checked.CheckedRecordField,
        ext: ?CheckedTypeId,
    ) Allocator.Error!void {
        var link_fields = fields;
        var link_ext = ext;
        while (true) {
            try into.appendSlice(self.gpa, link_fields);
            const next = link_ext orelse break;
            switch (self.types.payload(next)) {
                .record => |record| {
                    link_fields = record.fields;
                    link_ext = record.ext;
                },
                .alias => |alias| {
                    link_fields = &.{};
                    link_ext = alias.backing;
                },
                .empty_record,
                .tuple,
                .function,
                .nominal,
                .tag_union,
                .empty_tag_union,
                .flex,
                .rigid,
                .pending,
                .err,
                => break,
            }
        }
    }

    /// Pair a scheme tag union's variants with the use's by name, and match
    /// each pair's payloads.
    fn matchTagUnion(
        self: *Reifier,
        substitution: *Substitution,
        scheme_vars: []const CheckedTypeId,
        tags: []const checked.CheckedTag,
        ext: CheckedTypeId,
        use: TypeRef,
    ) Allocator.Error!void {
        var scheme_tags = std.ArrayList(checked.CheckedTag).empty;
        defer scheme_tags.deinit(self.gpa);
        try self.unionTags(&scheme_tags, tags, ext);

        var use_tags = std.ArrayList(checked.CheckedTag).empty;
        defer use_tags.deinit(self.gpa);
        switch (use.reader.types.payload(use.id)) {
            .tag_union => |use_union| try use.reader.unionTags(&use_tags, use_union.tags, use_union.ext),
            .alias,
            .record,
            .empty_record,
            .tuple,
            .function,
            .nominal,
            .empty_tag_union,
            .flex,
            .rigid,
            .pending,
            .err,
            => return,
        }

        for (scheme_tags.items) |variant| {
            for (use_tags.items) |fixed| {
                if (!self.sameTagLabel(variant.name, use.reader, fixed.name)) continue;
                const payloads = variant.argsSlice(self.types);
                const fixed_payloads = fixed.argsSlice(use.reader.types);
                if (payloads.len != fixed_payloads.len) break;
                for (payloads, fixed_payloads) |payload, fixed_payload| {
                    try self.matchType(substitution, scheme_vars, payload, use.reader.resolvedType(fixed_payload));
                }
                break;
            }
        }
    }

    /// The variants a tag union has, following its extension.
    fn unionTags(
        self: *Reifier,
        into: *std.ArrayList(checked.CheckedTag),
        tags: []const checked.CheckedTag,
        ext: CheckedTypeId,
    ) Allocator.Error!void {
        var link_tags = tags;
        var link_ext: ?CheckedTypeId = ext;
        while (true) {
            try into.appendSlice(self.gpa, link_tags);
            const next = link_ext orelse break;
            switch (self.types.payload(next)) {
                .tag_union => |more| {
                    link_tags = more.tags;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_tags = &.{};
                    link_ext = alias.backing;
                },
                .empty_tag_union,
                .record,
                .empty_record,
                .tuple,
                .function,
                .nominal,
                .flex,
                .rigid,
                .pending,
                .err,
                => break,
            }
        }
    }

    /// Whether a field label of this store names the field a label of another
    /// store names.
    ///
    /// Two stores intern independently, so one text lookup turns this store's
    /// id into that one's and the comparison stays a comparison of ids.
    fn sameFieldLabel(
        self: *Reifier,
        label: canonical.RecordFieldLabelId,
        other: *Reifier,
        other_label: canonical.RecordFieldLabelId,
    ) bool {
        if (self == other) return label == other_label;
        const here = other.names.lookupRecordFieldLabel(self.names.recordFieldLabelText(label)) orelse return false;
        return here == other_label;
    }

    /// Whether a tag label of this store names the variant a label of another
    /// store names.
    fn sameTagLabel(
        self: *Reifier,
        label: canonical.TagLabelId,
        other: *Reifier,
        other_label: canonical.TagLabelId,
    ) bool {
        if (self == other) return label == other_label;
        const here = other.names.lookupTagLabel(self.names.tagLabelText(label)) orelse return false;
        return here == other_label;
    }

    /// The identity of one instantiation: the types the callee's quantified
    /// variables were fixed to, in the scheme's own order.
    ///
    /// Digested from each bound type's canonical key rather than from its id,
    /// because an id is canonical only inside one module and two modules
    /// calling one generic function at one type share a row.
    fn instantiationKey(
        substitution: Substitution,
        scheme_vars: []const CheckedTypeId,
    ) [32]u8 {
        var hasher = std.crypto.hash.Blake3.init(.{});
        for (scheme_vars) |scheme_var| {
            // An unbound variable is a row, which no description names, so
            // every use of this definition keys the same row for it.
            const bound = substitution.get(scheme_var) orelse {
                hasher.update(&@as([32]u8, @splat(0)));
                continue;
            };
            hasher.update(&bound.reader.types.rootKey(bound.id).bytes);
        }
        var key: [32]u8 = undefined;
        hasher.final(&key);
        return key;
    }

    /// The concrete type a checked id names here, which for a quantified
    /// variable is what the call being walked fixed it to.
    fn resolvedType(self: *Reifier, type_id: CheckedTypeId) TypeRef {
        return self.fixedType(type_id) orelse .{ .reader = self, .id = type_id };
    }

    /// What a variable stands for here: what the call fixed a quantified
    /// variable to, or what a use fixed a nominal's declared variable to.
    fn fixedType(self: *Reifier, type_id: CheckedTypeId) ?TypeRef {
        if (self.substitution.get(type_id)) |fixed| return fixed;
        return self.nominal_args.get(type_id);
    }

    /// Record that the definition being walked calls this one, once however
    /// many calls it writes.
    fn recordCallee(self: *Reifier, key: DefinitionKey) Allocator.Error!void {
        for (self.walk.callees.items[self.walk.frame_base..]) |seen| {
            if (std.meta.eql(seen, key)) return;
        }
        try self.walk.callees.append(self.gpa, key);
    }

    /// Walk one definition's body, in a frame of its own so the calls it makes
    /// are recorded against it, and under an empty scope so it sees none of
    /// the caller's names. Takes ownership of `name`.
    ///
    /// The entry opens before the walk, so a call that reaches this same
    /// definition names it and stops rather than entering it a second time.
    fn describeDefinition(
        self: *Reifier,
        key: DefinitionKey,
        name: ?[]u8,
        instance: ?Instantiation,
        supplied: SuppliedEvidence,
        bound: []const BoundCallee,
        /// The function type of a root written at its own site, whose node
        /// holds the `Code` rather than the function. Null for a definition,
        /// whose node holds its own type.
        at: ?CheckedTypeId,
    ) Error!ConstNodeId {
        std.debug.assert(std.meta.eql(key.artifact, self.artifact.bytes));
        try self.walk.definitions.put(self.gpa, key, .{ .name = name, .node = null, .callees = &.{} });
        var described = false;
        // A walk that stopped leaves no half-described definition behind: a
        // later site meeting the same callee refuses it again rather than
        // reading an entry that never got a body.
        defer if (!described) self.walk.closeFailedDefinition(key);

        const outer_substitution = self.substitution;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        const outer_replay = self.replay;
        var replay: Replay = .{ .root = key.body, .region = self.bodies.expr(key.body).source_region };
        defer replay.deinit(self.gpa);
        self.substitution = if (instance) |fixed| fixed.substitution else .empty;
        self.substitution_uses = 0;
        self.evidence = supplied;
        self.bound = bound;
        self.bound_lambda = key.body;
        self.replay = if (at != null) &replay else null;
        defer {
            self.substitution = outer_substitution;
            self.substitution_uses = outer_uses;
            self.evidence = outer_evidence;
            self.bound = outer_bound;
            self.bound_lambda = outer_bound_lambda;
            self.replay = outer_replay;
        }

        const outer_base = self.walk.frame_base;
        self.walk.frame_base = self.walk.callees.items.len;
        defer {
            self.walk.callees.shrinkRetainingCapacity(self.walk.frame_base);
            self.walk.frame_base = outer_base;
        }

        const outer_scope = self.scope;
        const outer_versions = self.var_versions;
        const outer_loop = self.loop;
        self.scope = .empty;
        self.var_versions = .empty;
        self.loop = null;
        defer {
            self.scope.deinit(self.gpa);
            self.scope = outer_scope;
            self.var_versions.deinit(self.gpa);
            self.var_versions = outer_versions;
            self.loop = outer_loop;
        }

        // The row is walked under an empty scope, so a lambda lifted out of a
        // block takes what it captured as leading parameters. A root written
        // at its site is the exception: its signature is the `f` the site
        // fixed, which has room for neither an added parameter nor a capture.
        const node = if (key.curried)
            try self.curriedLambdaNode(key.body)
        else if (at) |fn_ty|
            try self.lambdaNodeAs(key.body, .in_scope, fn_ty)
        else
            try self.lambdaNodeAs(key.body, .parameter, null);
        const callees = try self.gpa.dupe(DefinitionKey, self.walk.callees.items[self.walk.frame_base..]);

        const entry = self.walk.definitions.getPtr(key).?;
        entry.node = node;
        entry.callees = callees;
        described = true;
        return node;
    }

    /// The `{ defs, root }` a site holds, for a root that is a definition:
    /// what the root calls seeds the table.
    fn siteNode(self: *Reifier, root: ConstNodeId, key: DefinitionKey) Error!ConstNodeId {
        var rows = try self.definitionRows(
            self.walk.definitions.get(key).?.callees,
            self.bodies.expr(key.body).source_region,
        );
        defer rows.deinit(self.gpa);
        return self.recordOf(&rows, root);
    }

    /// One `Def` row per definition the seeds reach, callee before caller.
    ///
    /// A definition is written once its own callees are, and one already
    /// written is skipped, so a caller never precedes a callee. A cycle has no
    /// such order to keep, and the definition the cycle was entered through
    /// comes last of the cycle.
    ///
    /// The described root is a row only when something calls it, which is why
    /// a recursive function has a row to resolve its own name against and
    /// every other description carries no copy of its root.
    fn definitionRows(
        self: *Reifier,
        seeds: []const DefinitionKey,
        region: base.Region,
    ) Error!std.ArrayList(ConstNodeId) {
        var rows = std.ArrayList(ConstNodeId).empty;
        errdefer rows.deinit(self.gpa);
        var written = std.AutoHashMapUnmanaged(DefinitionKey, void).empty;
        defer written.deinit(self.gpa);
        for (seeds) |seed| try self.writeDefinitionRow(seed, &written, &rows, region);
        return rows;
    }

    fn writeDefinitionRow(
        self: *Reifier,
        key: DefinitionKey,
        written: *std.AutoHashMapUnmanaged(DefinitionKey, void),
        rows: *std.ArrayList(ConstNodeId),
        region: base.Region,
    ) Error!void {
        if ((try written.getOrPut(self.gpa, key)).found_existing) return;
        const definition = self.walk.definitions.get(key) orelse
            return self.rejectError(.unresolved_reference, region, "this call");
        for (definition.callees) |callee| try self.writeDefinitionRow(callee, written, rows, region);
        const node = definition.node orelse
            return self.rejectError(.unresolved_reference, region, "this call");
        const name = definition.name orelse
            return self.rejectError(.unresolved_reference, region, "this call");
        // `Code.Def` is `{ ir, name }`, and a constant record's fields are
        // restored in label order.
        try rows.append(self.gpa, try self.store.append(.{ .record = &.{ node, try self.strNode(name) } }));
    }

    /// `Code`'s backing: the table, then the described body.
    fn recordOf(self: *Reifier, rows: *std.ArrayList(ConstNodeId), root: ConstNodeId) Allocator.Error!ConstNodeId {
        const defs = try self.store.append(.{ .list = .{ .nodes = rows.items } });
        return self.store.append(.{ .record = &.{ defs, root } });
    }

    /// Every operator in Roc is a method call, so this arm carries both the
    /// `Binop`/`Unary` forms and ordinary `Call`s.
    fn dispatchNode(
        self: *Reifier,
        plan_id: ?static_dispatch.StaticDispatchPlanId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const id = plan_id orelse return self.reject(.unresolved_reference, region, "this call");
        const plan = self.plans.plans[@backingInt(id)];
        const method = self.names.methodNameText(plan.method);

        switch (plan.resolution) {
            // The checker picked a compiler-derived implementation, so there is
            // no Roc body behind this name.
            .structural => |derivation| return self.structuralDispatchNode(plan, derivation, method, meta, region),
            .checked_error, .@"unreachable" => return self.reject(.unresolved_reference, region, "this call"),
            // The body forwards this obligation to its own evidence param. The
            // call that instantiated the body says what discharged it, so a
            // derived codec describes as one here too rather than as a call to
            // a name with no definition behind it.
            .evidence_dependent => |forwarded| {
                if (self.forwardedDerivation(forwarded.index)) |derivation| {
                    return self.structuralDispatchNode(plan, derivation, method, meta, region);
                }
            },
            .direct_pending, .direct_closed, .direct_parametric => {},
        }

        const operands = plan.argsSlice(self.plans);
        const args = try self.gpa.alloc(ConstNodeId, operands.len);
        defer self.gpa.free(args);
        for (operands, 0..) |operand, index| {
            args[index] = switch (operand) {
                .checked_expr => |child| try self.irNode(child),
                .generated_numeral => |literal| try self.generatedNumeralNode(literal, region),
                .generated_quote => |literal| try self.generatedQuoteNode(literal, region),
                .generated_interpolation_segments => return self.reject(.unsupported_expression, region, "a custom string interpolation"),
            };
        }

        if (operands.len == 2 and self.operators.isBinop(plan.method)) {
            const op = try self.strNode(method);
            return self.tag("Binop", &.{ op, args[0], args[1], meta });
        }
        if (operands.len == 2) {
            if (self.operators.rangeEnd(plan.method)) |end| {
                return self.tag("Range", &.{ args[0], args[1], try self.tag(end, &.{}), meta });
            }
        }
        if (operands.len == 1) {
            if (self.operators.unaryOp(plan.method)) |op_name| {
                const op = try self.strNode(op_name);
                return self.tag("Unary", &.{ op, args[0], meta });
            }
        }

        const spelled = try self.calleeName(plan, method);
        defer self.gpa.free(spelled);
        // The method's body goes into the table the way a plain call's does,
        // so the name the `Call` carries resolves against a row rather than
        // against nothing.
        //
        // A method whose body the walk cannot describe keeps the bare name,
        // the way a builtin does. That is what a target primitive needs: a
        // `Sampler.texture` whose Roc body stands in for a GPU fetch on the
        // CPU is named here and emitted by the translator that knows the name.
        // A plain call keeps no bare name, because it never had one a
        // translator could resolve on its own.
        const callee = self.describedDispatch(plan, spelled, region) catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.Rejected => spelled,
        };
        const name = try self.strNode(callee);
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return self.tag("Call", &.{ name, list, meta });
    }

    /// The name a dispatch's callee takes, with its body described into the
    /// table when the walk can describe it.
    ///
    /// A walk that stopped leaves nothing behind: the frame's callees go back
    /// to what they were, so the table names no row that was never written,
    /// and the site's first refusal is still the one it reports.
    fn describedDispatch(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        spelled: []const u8,
        region: base.Region,
    ) Error![]const u8 {
        const callees = self.walk.callees.items.len;
        const rejection = self.walk.rejection;
        errdefer {
            self.walk.callees.shrinkRetainingCapacity(callees);
            self.walk.rejection = rejection;
        }
        const target = switch (try self.dispatchTarget(plan, spelled, region)) {
            .definition => |found| found,
            .provided => |name| return name,
            .spelled => return spelled,
        };
        return self.calledDefinition(.{ .definition = target }, region);
    }

    /// One instantiation edge: the target the checker chose, and the reader of
    /// the module that recorded it.
    ///
    /// The reader is half the answer because every id on the node is that
    /// module's: the node itself, the nested evidence it points at, and the
    /// types it fixed the target's variables to.
    const DispatchEdge = struct {
        reader: *Reifier,
        node: static_dispatch.EvidenceNode,
    };

    /// The instantiation edge this dispatch was discharged through, or null
    /// when nothing names a target: a derived implementation, a rejected site,
    /// or an obligation the walk holds no answer for.
    fn dispatchEdge(self: *Reifier, plan: static_dispatch.StaticDispatchCallPlan) ?DispatchEdge {
        switch (plan.resolution) {
            .direct_closed, .direct_parametric => |direct| {
                return .{ .reader = self, .node = self.plans.evidenceNode(direct.evidence) };
            },
            // The body forwards the obligation to its own evidence param, so
            // the target is named by the call that instantiated the body and
            // recorded in that call's own tables.
            .evidence_dependent => |forwarded| {
                if (forwarded.index.depth != 0) return null;
                const caller = self.evidence.reader orelse return null;
                if (forwarded.index.index >= self.evidence.entries.len) return null;
                return switch (self.evidence.entries[forwarded.index.index].resolution) {
                    .direct => |node_id| .{ .reader = caller, .node = caller.plans.evidenceNode(node_id) },
                    .constraint,
                    .structural,
                    .from_callable,
                    .from_scheme,
                    .checked_error,
                    .unreachable_value,
                    => null,
                };
            },
            .direct_pending, .structural, .checked_error, .@"unreachable" => return null,
        }
    }

    /// What a dispatch's callee is from the walk's side.
    const DispatchCallee = union(enum) {
        /// A body the walk describes into the table.
        definition: CalleeTarget,
        /// A function the compiler provides, which the description names and
        /// leaves to the translator to resolve.
        provided: []const u8,
        /// Nothing the walk reaches, so the site keeps the name it spelled.
        spelled,
    };

    /// What this dispatch reaches: a definition to describe, a builtin to
    /// name, or nothing, which is a method written inside another function or
    /// one no edge names a target for.
    ///
    /// `spelled` is what the `Call` names the callee, which the row answers to.
    fn dispatchTarget(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        spelled: []const u8,
        region: base.Region,
    ) Error!DispatchCallee {
        const edge = self.dispatchEdge(plan) orelse return .spelled;
        return self.methodTargetCallee(edge.reader, edge.node.target, .{ .edge = edge.node }, spelled, region);
    }

    /// How a call fixes a method's quantified variables and discharges its
    /// obligations.
    ///
    /// A dispatch the checker planned reads both off its edge. A method the
    /// walk resolved itself has no edge, because no call site wrote it: the
    /// compiler's own derivation reached it. What that form has instead is the
    /// receiver, the value the derivation is comparing or hashing, whose type
    /// the walk knows and whose shape fixes what the method quantifies.
    const MethodFixing = union(enum) {
        edge: static_dispatch.EvidenceNode,
        receiver: TypeRef,
    };

    /// What one method target is from the walk's side.
    ///
    /// `owner` is the reader of the module that recorded the target, which is
    /// the module whose ids the target is named in.
    fn methodTargetCallee(
        self: *Reifier,
        owner: *Reifier,
        target: static_dispatch.MethodTarget,
        fixing: MethodFixing,
        spelled: []const u8,
        region: base.Region,
    ) Error!DispatchCallee {
        const procedure = switch (target.kind) {
            .procedure => |procedure| procedure,
            .local_proc, .structural => return .spelled,
        };
        const found = owner.methodDefinition(procedure.template, target.def_idx) orelse return .spelled;
        switch (found) {
            .provided => |name| return .{ .provided = name },
            .here, .away => {},
        }
        const reader = switch (found) {
            .here => owner,
            .away => |definition| try self.walk.reader(definition.module),
            .provided => unreachable,
        };
        var instance = switch (fixing) {
            .edge => |node| try owner.dispatchInstantiation(reader, found.template(), node, region),
            .receiver => |receiver| try reader.receiverInstantiation(found.template(), receiver, region),
        };
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        return .{
            .definition = .{
                .key = .{
                    .artifact = reader.artifact.bytes,
                    .body = found.body(),
                    .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
                },
                .spelling = .{ .written = spelled },
                .reader = reader,
                .instantiation = instance,
                .evidence = switch (fixing) {
                    .edge => |node| switch (node.nested) {
                        .resolved => .{ .reader = owner, .entries = owner.plans.nestedEvidence(node) },
                        // The edge derives the target's evidence from its
                        // callable rather than recording it, so the walk of the
                        // body has no answer to read and describes a forwarded
                        // obligation as the call it is.
                        .from_callable => .{},
                    },
                    // A derivation records no evidence, because the checker
                    // planned no call, so an obligation inside the body
                    // describes as the call it is.
                    .receiver => .{},
                },
            },
        };
    }

    /// Where a method's body lives: this module's tables, another module's
    /// export rows, or nowhere the walk reads, in which case the compiler
    /// provides it and the description carries its name.
    const MethodDefinition = union(enum) {
        here: struct { template: checked.CheckedProcedureTemplate, body: CheckedExprId },
        away: ForeignDefinition,
        provided: []const u8,

        fn template(self: MethodDefinition) checked.CheckedProcedureTemplate {
            return switch (self) {
                .here => |local| local.template,
                .away => |definition| definition.template,
                .provided => unreachable,
            };
        }

        fn body(self: MethodDefinition) CheckedExprId {
            return switch (self) {
                .here => |local| local.body,
                .away => |definition| definition.body,
                .provided => unreachable,
            };
        }
    };

    /// The template and body one method target names, the name a builtin
    /// answers to, or null when the walk stops there: a module it cannot read
    /// has no body to describe and no export name to read one from.
    fn methodDefinition(
        self: *Reifier,
        template_ref: canonical.ProcedureTemplateRef,
        def_idx: CIR.Def.Idx,
    ) ?MethodDefinition {
        if (std.meta.eql(template_ref.artifact.bytes, self.artifact.bytes)) {
            const templates = self.procedure_templates.templates.items;
            const raw = @backingInt(template_ref.template);
            if (raw >= templates.len) return null;
            const template = templates[raw];
            const body_id = switch (template.body) {
                .checked_body => |body| body,
                .intrinsic_wrapper, .entry_wrapper, .unimplemented => return null,
            };
            return .{ .here = .{ .template = template, .body = self.bodies.body(body_id).root_expr } };
        }
        const definition = self.walk.foreign.findExported(template_ref.artifact, def_idx) orelse return null;
        if (definition.module.env.module_role == .builtin) {
            return .{ .provided = (providedName(definition) orelse return null).text };
        }
        return .{ .away = definition };
    }

    /// What this dispatch fixes the method's quantified variables to, or null
    /// when the method has none.
    ///
    /// The edge records one type per variable in the scheme's own order, so
    /// there is nothing to match: the pairs are read off the edge. Each is
    /// named in the caller's store and resolved through the caller's own
    /// substitution, because a generic body dispatching in its own variables
    /// keys its callee's row by what the outer call fixed them to.
    fn dispatchInstantiation(
        self: *Reifier,
        reader: *Reifier,
        template: checked.CheckedProcedureTemplate,
        node: static_dispatch.EvidenceNode,
        region: base.Region,
    ) Error!?Instantiation {
        const scheme_vars = reader.schemeVars(template);
        if (scheme_vars.len == 0) return null;
        const fixed = self.plans.targetSubstitution(node);
        if (fixed.len != scheme_vars.len) {
            return self.rejectError(.unresolved_type, region, "a call to a generic method this call does not fix");
        }

        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        for (scheme_vars, fixed) |scheme_var, use| {
            try substitution.put(self.gpa, scheme_var, self.resolvedType(use));
        }
        return .{ .substitution = substitution, .key = instantiationKey(substitution, scheme_vars) };
    }

    /// What the receiver fixes a generic method's quantified variables to, or
    /// null when the method has none.
    ///
    /// A method's first parameter is the value it is called on, and a
    /// derivation reached the method through that value's type, so pairing the
    /// two binds what the scheme quantifies by shape. `self` reads the
    /// method's scheme type, and the receiver names its own type in the store
    /// of whichever module walked it.
    ///
    /// The guard is `instantiationOf`'s: every quantified variable bound, or a
    /// report. A method quantified over something its receiver does not
    /// mention leaves a hole in the body, and the name alone says more than a
    /// row described at a type the walk invented.
    fn receiverInstantiation(
        self: *Reifier,
        template: checked.CheckedProcedureTemplate,
        receiver: TypeRef,
        region: base.Region,
    ) Error!?Instantiation {
        const scheme_vars = self.schemeVars(template);
        if (scheme_vars.len == 0) return null;
        const scheme_fn = self.functionOf(template.checked_fn_root) orelse
            return self.rejectError(.unresolved_type, region, "a generic method whose type is not a function");
        if (scheme_fn.args.len == 0) {
            return self.rejectError(.unresolved_type, region, "a generic method that names no receiver");
        }

        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        try self.matchType(&substitution, scheme_vars, scheme_fn.args[0], receiver);

        for (scheme_vars) |scheme_var| {
            if (!substitution.contains(scheme_var)) {
                return self.rejectError(.unresolved_type, region, "a generic method this receiver does not fix");
            }
        }
        return .{ .substitution = substitution, .key = instantiationKey(substitution, scheme_vars) };
    }

    /// A call the checker discharged with a derived implementation. Equality
    /// and hashing have recipes the IR can spell out; a codec's has to agree
    /// with JSON, Postgres or Arrow rather than with Roc, so it stays symbolic
    /// and the stage expands it.
    fn structuralDispatchNode(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        derivation: static_dispatch.StructuralDerivation,
        method: []const u8,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const operands = plan.argsSlice(self.plans);
        const exprs = try self.gpa.alloc(CheckedExprId, operands.len);
        defer self.gpa.free(exprs);
        for (operands, 0..) |operand, index| {
            exprs[index] = switch (operand) {
                .checked_expr => |child| child,
                .generated_numeral, .generated_quote, .generated_interpolation_segments => return self.reject(
                    .unsupported_expression,
                    region,
                    "a compiler-generated argument",
                ),
            };
        }

        switch (derivation) {
            .equality => {
                if (exprs.len != 2) {
                    return self.reject(.unsupported_expression, region, "a derived equality of this arity");
                }
                return self.structuralEqNode(exprs[0], exprs[1], false, meta, region);
            },
            .hash => {
                if (exprs.len != 2) {
                    return self.reject(.unsupported_expression, region, "a derived hash of this arity");
                }
                return self.structuralHashNode(exprs[0], exprs[1], meta, region);
            },
            // A codec's recipe has to agree with JSON, Postgres or Arrow, and
            // a derived `map`'s with the payload slot the checker picked, so
            // all four stay symbolic and the stage expands them.
            .parser, .encoder, .map, .map_effectful => {
                const args = try self.irNodes(exprs);
                defer self.gpa.free(args);
                return self.derivedNode(method, plan.dispatcher_ty, args, meta, region);
            },
        }
    }

    /// The compiler-derived implementation the instantiating call supplied for
    /// one forwarded obligation, or null when it supplied a Roc body instead.
    ///
    /// A non-zero depth names an evidence param of a callable further out than
    /// the one being walked, and the walk holds only the innermost, so that
    /// case reads as unknown and the dispatch describes as an ordinary call.
    fn forwardedDerivation(
        self: *Reifier,
        chain: static_dispatch.EvidenceChainIndex,
    ) ?static_dispatch.StructuralDerivation {
        if (chain.depth != 0) return null;
        if (chain.index >= self.evidence.entries.len) return null;
        return switch (self.evidence.entries[chain.index].resolution) {
            .structural => |structural| structural.derivation,
            .direct,
            .constraint,
            .from_callable,
            .from_scheme,
            .checked_error,
            .unreachable_value,
            => null,
        };
    }

    /// `Type.method` when the dispatcher names a type, so a stage can tell
    /// `F32.sin` from a same-named method on another type.
    fn calleeName(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        method: []const u8,
    ) Allocator.Error![]u8 {
        if (self.typeName(plan.dispatcher_ty)) |owner| {
            return std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ owner, method });
        }
        return self.gpa.dupe(u8, method);
    }

    fn typeName(self: *Reifier, type_id: CheckedTypeId) ?[]const u8 {
        // A `where`-constrained body dispatches on a quantified variable, so
        // the name a call carries is the one the instantiation fixed.
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.typeName(resolved.id);
        return switch (self.types.payload(resolved.id)) {
            .alias => |alias| self.typeName(alias.backing),
            .nominal => |nominal| self.names.typeNameText(nominal.name),
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .tuple,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => null,
        };
    }

    fn irNodes(self: *Reifier, exprs: []const CheckedExprId) Error![]ConstNodeId {
        const nodes = try self.gpa.alloc(ConstNodeId, exprs.len);
        errdefer self.gpa.free(nodes);
        for (exprs, 0..) |child, index| nodes[index] = try self.irNode(child);
        return nodes;
    }

    /// Where a name bound to a compile-time constant leads: the reader that
    /// holds the value's body, and the body.
    ///
    /// The checker resolves such a name to a `ConstRef`, and the template that
    /// ref names holds the checked body the value was written as. A name the
    /// running program computes resolves to something else and answers null,
    /// which is what keeps the boundary where C9 drew it.
    const ConstantDefinition = struct {
        reader: *Reifier,
        body: CheckedExprId,
    };

    fn constantDefinition(
        self: *Reifier,
        resolved: ?checked.ResolvedValueRefId,
    ) Allocator.Error!?ConstantDefinition {
        const id = resolved orelse return null;
        const const_ref = switch (self.value_refs.callableTarget(id).ref) {
            .top_level_const, .imported_const => |use| use.const_ref,
            .selected_hoisted_const => |selected| selected.const_use.const_ref,
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .local_proc,
            .top_level_proc,
            .imported_proc,
            .hosted_proc,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            .promoted_top_level_proc,
            => return null,
        };
        if (std.meta.eql(const_ref.artifact.bytes, self.artifact.bytes)) {
            const body = constantBody(self.const_templates, self.const_bodies, const_ref) orelse return null;
            return .{ .reader = self, .body = body };
        }
        const away = self.walk.foreign.findConstant(const_ref) orelse return null;
        return .{ .reader = try self.walk.reader(away.module), .body = away.body };
    }

    /// The value a name holds, described where the name stands.
    ///
    /// The fold is by value: a translator never learns that a name stood
    /// between the body and the value, the way a `Call` names a definition
    /// rather than applying a function value. So there is no capture to lower
    /// and no node to add.
    fn foldedConstant(
        self: *Reifier,
        resolved: ?checked.ResolvedValueRefId,
        region: base.Region,
    ) Error!?ConstNodeId {
        const definition = try self.constantDefinition(resolved) orelse return null;
        if (!try self.nameHoldsConstant(resolved)) return null;

        const reader = definition.reader;
        try reader.folding.put(reader.gpa, definition.body, {});
        defer _ = reader.folding.remove(definition.body);
        const outer = reader.folded_origin;
        reader.folded_origin = self.folded_origin orelse .{
            .module = self.env.module_name,
            .info = self.env.calcAuthoredRegionInfo(region),
        };
        defer reader.folded_origin = outer;
        return try reader.irNode(definition.body);
    }

    fn lookupNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        resolved: ?checked.ResolvedValueRefId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse
            return self.reject(.unresolved_reference, region, "this reference");
        const binding = self.lookupBinding(binder) orelse try self.replayBinding(binder) orelse {
            if (try self.foldedConstant(resolved, region)) |folded| return folded;
            return self.reject(.capture, region, self.binderName(binder));
        };
        return switch (binding.kind) {
            .param => self.tag("Param", &.{ try self.strNode(binding.name), meta }),
            .local => self.tag("Local", &.{ try self.strNode(binding.name), meta }),
            // The literal carries the region of the argument the call wrote,
            // which is where the value the stage reads was actually written.
            .constant => |node| node,
            // The binding holds a function, and the `Ir` is first order. It
            // has a description only where the call that runs it folds it into
            // one node, which is the use this name was not.
            .function, .callee => self.reject(.unsupported_expression, region, "a reference to a function value"),
        };
    }

    fn blockNode(
        self: *Reifier,
        statements: []const CheckedStatementId,
        final_expr: CheckedExprId,
        escapes: bool,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (statements.len == 0) {
            return if (escapes) self.tailNode(final_expr, meta) else self.irNode(final_expr);
        }

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        return self.statementsNode(
            .{ .statements = statements, .ending = .{ .expr = final_expr }, .escapes = escapes },
            meta,
            region,
        );
    }

    /// One `var` a branch writes, carried out of the branches that write it.
    const Join = struct {
        binder: checked.PatternBinderId,
        ty: ConstNodeId,
        meta: ConstNodeId,
    };

    /// What a run of statements hands back when it runs out.
    const Ending = union(enum) {
        /// The expression the block ends on.
        expr: CheckedExprId,
        /// The `var`s a branch writes, read at the version the branch left
        /// them at. A branch of a statement `if` hands back no value of its
        /// own, so what it hands the join underneath it is this.
        joined: []const Join,
        /// An expression the block ends on whose value is discarded, and the
        /// `var`s after it. A loop body written `for x in xs { if .. { .. } }`
        /// ends on that `if`, which is a statement wearing the last
        /// expression's place.
        trailing: struct { expr: CheckedExprId, joins: []const Join },
        /// A continuation already described: the body of a root that the
        /// statements it reads from around it are replayed over.
        node: ConstNodeId,
    };

    /// What runs after a statement: the statements its block has left, what
    /// the block ends on, and whether a `return` or a `break` written here
    /// has a description.
    ///
    /// It has one where the value of this run of statements leaves the block
    /// it was written in, which is the function's tail and a loop's turn.
    /// Anywhere else a transfer would skip work no node skips.
    const Rest = struct {
        statements: []const CheckedStatementId,
        ending: Ending,
        escapes: bool,

        fn after(self: Rest) Rest {
            return .{ .statements = self.statements[1..], .ending = self.ending, .escapes = self.escapes };
        }
    };

    /// The statements a block has left to run, and the expression it ends on.
    ///
    /// A statement wraps whatever comes after it, so the walk descends rather
    /// than iterates: a `Let` nests rightward, a destructuring binding nests
    /// several deep for the one statement it was written as, and a branch
    /// that returns early takes everything after it as its alternative.
    fn statementsNode(
        self: *Reifier,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (rest.statements.len == 0) {
            return switch (rest.ending) {
                .expr => |final_expr| if (rest.escapes)
                    self.tailNode(final_expr, meta)
                else
                    self.irNode(final_expr),
                .joined => |joins| self.joinedNode(joins, region),
                .node => |node| node,
                .trailing => |trailing| self.discardedNode(
                    trailing.expr,
                    .{ .statements = &.{}, .ending = .{ .joined = trailing.joins }, .escapes = rest.escapes },
                    meta,
                    region,
                ),
            };
        }

        const statement = self.bodies.statement(rest.statements[0]);
        refused: switch (statement.data) {
            .decl => |decl| return self.declNode(decl.pattern, decl.expr, rest.after(), meta, region),
            // A `var` binds a name the way any other binding does. What
            // makes it a `var` is that an assignment may follow it, and the
            // description of that is a version of its own.
            .var_ => |decl| return self.declNode(decl.pattern, decl.expr, rest.after(), meta, region),
            .reassign => |assignment| return self.reassignNode(
                assignment.pattern,
                assignment.expr,
                assignment.reassigned_binders,
                rest.after(),
                meta,
                region,
            ),
            // A type-level statement names a type for the checker and leaves
            // no value behind, so the description passes over it rather than
            // refusing the block it sits in. `Shape : value` before a derived
            // dispatch is the shape that makes this worth handling.
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            => return self.statementsNode(rest.after(), meta, region),
            // An `expect` asserts and hands back nothing, so the description
            // passes over it the way it passes over a type annotation. A
            // translator emits a target, and an assertion the author wrote
            // for Roc's own test run has no place in one.
            .expect => return self.statementsNode(rest.after(), meta, region),
            // A promoted local function evaluates nothing where it is
            // written. Every use of its name resolves to its procedure.
            .promoted_proc => return self.statementsNode(rest.after(), meta, region),
            // `return` hands its value back as the function's, and the
            // statements after it do not run.
            .return_ => |returned| {
                if (!rest.escapes) break :refused;
                return self.returnNode(returned.expr, meta);
            },
            // `break` settles the loop at the state it has reached, and the
            // statements after it do not run either.
            .break_ => {
                if (!rest.escapes) break :refused;
                return self.breakNode(meta, region);
            },
            .expr => |discarded| return self.discardedNode(discarded, rest.after(), meta, region),
            .for_ => |loop| return self.forNode(loop.pattern, loop.expr, loop.body, rest.after(), meta, region),
            .while_ => |loop| return self.whileNode(loop.cond, loop.body, rest.after(), meta, region),
            // `while Bool.True { .. }` reaches the walk as one of these two,
            // which carry what a `while_` carries, so the three describe
            // through one call. Zig types each union payload on its own, so
            // they take an arm each.
            .infinite_loop => |loop| return self.whileNode(loop.cond, loop.body, rest.after(), meta, region),
            .breakable_loop => |loop| return self.whileNode(loop.cond, loop.body, rest.after(), meta, region),
            .pending,
            .var_uninitialized,
            .crash,
            .dbg,
            .import_,
            .runtime_error,
            => break :refused,
        }
        return self.reject(.unsupported_expression, region, statementFormName(statement.data));
    }

    /// An expression whose value leaves the block it was written in: the
    /// reified function's own value, or, inside a loop, the turn's.
    ///
    /// `meta` is the position's rather than the expression's, because a
    /// transfer has the type of the branch it stands in and none of its own.
    fn tailNode(self: *Reifier, expr_id: CheckedExprId, meta: ConstNodeId) Error!ConstNodeId {
        const expr = self.bodies.expr(expr_id);
        const region = expr.source_region;
        return switch (expr.data) {
            .return_ => |returned| self.returnNode(returned.expr, meta),
            .break_ => self.breakNode(meta, region),
            .block => |block| self.blockNode(block.statements, block.final_expr, true, meta, region),
            .if_ => |conditional| self.ifNode(conditional.branches, conditional.final_else, true, meta),
            .match_ => |matched| self.matchNode(matched.cond, matched.branches, true, meta),
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => self.valueNode(expr_id, meta, region),
        };
    }

    /// `return e`.
    ///
    /// Outside a loop the continuation is the statements written after it,
    /// which a branch carries, so the description is the value alone and a
    /// target with no control flow at all still reads it. Inside a loop the
    /// continuation is the turns that have not run, which no branch says, so
    /// the transfer is stated.
    fn returnNode(self: *Reifier, value_id: CheckedExprId, meta: ConstNodeId) Error!ConstNodeId {
        if (self.loop == null) return self.tailNode(value_id, meta);
        return self.tag("Return", &.{ try self.irNode(value_id), meta });
    }

    /// `break`: the loop settles on the state its `var`s have reached here.
    fn breakNode(self: *Reifier, meta: ConstNodeId, region: base.Region) Error!ConstNodeId {
        const loop = self.loop orelse return self.reject(.unsupported_expression, region, "break");
        return self.tag("Break", &.{ try self.joinedNode(loop.joins, region), meta });
    }

    /// An expression in a position whose value leaves the block, with any
    /// transfer written inside it lifted out past it.
    fn valueNode(
        self: *Reifier,
        expr_id: CheckedExprId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (self.liftable(expr_id)) |lifted| {
            return self.escapingNode(lifted, .{ .valued = expr_id }, meta, region);
        }
        return self.irNode(expr_id);
    }

    /// A statement whose value is discarded.
    ///
    /// A branch that assigns a `var` hands back the version it settled it to,
    /// and one that transfers hands back what the transfer takes. What is
    /// left computed a value and threw it away, which is a binding nothing
    /// reads: the order it was written in and whatever it diverges on both
    /// stay, and no node is needed for either.
    fn discardedNode(
        self: *Reifier,
        expr_id: CheckedExprId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var joins = std.ArrayList(Join).empty;
        defer joins.deinit(self.gpa);
        try self.collectAssigned(&joins, expr_id);
        if (joins.items.len != 0) return self.joinNode(expr_id, joins.items, rest, meta, region);

        if (rest.escapes) {
            if (self.escapesEarly(expr_id)) return self.tailNode(expr_id, meta);
            if (self.branchesEscape(expr_id)) {
                return self.escapingNode(expr_id, .{ .discarded = rest }, meta, region);
            }
        }

        const value = try self.irNode(expr_id);
        const name = try self.strNode(try self.inventedName());
        const under = try self.statementsNode(rest, meta, region);
        return self.tag("Let", &.{ name, value, under, meta });
    }

    /// The `var`s this expression's branches assign, each once.
    ///
    /// A `var` declared inside the expression is not one of them: it is not
    /// in scope out here, so nothing under the branches can read it and
    /// there is nothing to carry out.
    fn collectAssigned(self: *Reifier, joins: *std.ArrayList(Join), expr_id: CheckedExprId) Error!void {
        switch (self.bodies.expr(expr_id).data) {
            .block => |block| {
                for (block.statements) |statement_id| {
                    try self.collectAssignedStatement(joins, statement_id);
                }
                try self.collectAssigned(joins, block.final_expr);
            },
            .if_ => |conditional| {
                for (conditional.branches) |branch| try self.collectAssigned(joins, branch.body);
                try self.collectAssigned(joins, conditional.final_else);
            },
            .match_ => |matched| {
                for (matched.branches) |branch| try self.collectAssigned(joins, branch.value);
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => {},
        }
    }

    fn collectAssignedStatement(
        self: *Reifier,
        joins: *std.ArrayList(Join),
        statement_id: CheckedStatementId,
    ) Error!void {
        switch (self.bodies.statement(statement_id).data) {
            .reassign => |assignment| {
                if (assignment.reassigned_binders.len != 1) return;
                const binder = assignment.reassigned_binders[0];
                if (self.lookupBinding(binder) == null) return;
                for (joins.items) |join| {
                    if (join.binder == binder) return;
                }
                const value = self.bodies.expr(assignment.expr);
                const ty = try self.tyNode(value.ty, value.source_region);
                const meta = try self.metaNode(ty, value.source_region);
                try joins.append(self.gpa, .{ .binder = binder, .ty = ty, .meta = meta });
            },
            .expr => |discarded| try self.collectAssigned(joins, discarded),
            .decl => |decl| try self.collectAssigned(joins, decl.expr),
            .var_ => |decl| try self.collectAssigned(joins, decl.expr),
            // A promoted function is self-contained, so it assigns no `var`
            // of the body it is written in.
            .promoted_proc,
            .pending,
            .var_uninitialized,
            .crash,
            .dbg,
            .expect,
            .for_,
            .while_,
            .infinite_loop,
            .breakable_loop,
            .break_,
            .return_,
            .import_,
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            .runtime_error,
            => {},
        }
    }

    /// An `if` or a `match` whose branches assign a `var`, described as the
    /// versions it settles them to.
    ///
    /// The `Ir` has no assignment, so the branch hands back what it wrote and
    /// the binding goes underneath it: over a `var $x`, `if c { $x = 1 }`
    /// followed by the rest of the body describes as
    /// `Let($x#1, If(c, 1, $x), rest)`. Several `var`s travel together as a
    /// tuple, because one `If` per `var` would describe each branch once per
    /// `var`.
    fn joinNode(
        self: *Reifier,
        expr_id: CheckedExprId,
        joins: []const Join,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const carried = try self.joinMeta(joins, region);
        // A branch of the join may leave the loop instead of settling: Roc's
        // own `fold_until` writes its state and breaks in the same branch.
        // Outside a loop a transfer here has nowhere to go that a branch does
        // not already carry, so it stays refused.
        const escapes = rest.escapes and self.loop != null;
        const settled = try self.joinBranches(expr_id, joins, carried, escapes, region);
        return self.settledNode(settled, joins, carried, rest, meta, region);
    }

    /// What an `if`, a `match` or a loop settled its `var`s to, bound under
    /// the node that settled them.
    ///
    /// One `var` is the node's whole value. Several travel as a tuple, so
    /// they are taken apart one `Index` at a time, in the order the tuple
    /// holds them.
    fn settledNode(
        self: *Reifier,
        settled: ConstNodeId,
        joins: []const Join,
        carried: ConstNodeId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // A loop that carries nothing settles nothing, so it binds a name
        // nothing reads, which is what any discarded statement does.
        if (joins.len == 0) {
            const name = try self.strNode(try self.inventedName());
            const under = try self.statementsNode(rest, meta, region);
            return self.tag("Let", &.{ name, settled, under, meta });
        }

        if (joins.len == 1) {
            const name = try self.strNode(try self.nextVersionName(joins[0].binder, region));
            const under = try self.statementsNode(rest, meta, region);
            return self.tag("Let", &.{ name, settled, under, meta });
        }

        const tuple = try self.strNode(try self.inventedName());
        const read = try self.tag("Local", &.{ tuple, carried });
        const names = try self.gpa.alloc(ConstNodeId, joins.len);
        defer self.gpa.free(names);
        const reads = try self.gpa.alloc(ConstNodeId, joins.len);
        defer self.gpa.free(reads);
        for (joins, 0..) |join, position| {
            const index = try self.store.append(.{ .scalar = .{ .u64 = @intCast(position) } });
            reads[position] = try self.tag("Index", &.{ read, index, join.meta });
            names[position] = try self.strNode(try self.nextVersionName(join.binder, region));
        }

        var node = try self.statementsNode(rest, meta, region);
        var index = joins.len;
        while (index > 0) {
            index -= 1;
            node = try self.tag("Let", &.{ names[index], reads[index], node, meta });
        }
        return self.tag("Let", &.{ tuple, settled, node, meta });
    }

    /// `for item in source { .. }`, as the fold it is.
    ///
    /// The `Ir` has no assignment, so the loop carries the `var`s its body
    /// writes from one turn to the next: the turn reads the state it starts
    /// from, and hands back the state the next turn starts from. What the
    /// last turn leaves is what the statements under the loop read.
    fn forNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        source_id: CheckedExprId,
        body_id: CheckedExprId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var joins = std.ArrayList(Join).empty;
        defer joins.deinit(self.gpa);
        try self.collectAssigned(&joins, body_id);

        const state = try self.joinMeta(joins.items, region);
        const source = try self.irNode(source_id);
        const initials = try self.initialNodes(joins.items, region);
        defer self.gpa.free(initials);

        const scope_base = self.scope.items.len;
        const item = try self.strNode(try self.bindLocal(pattern_id, region));
        const carried = try self.carriedNodes(joins.items, initials, region);
        const body = try self.loopBodyNode(body_id, joins.items, state, region);
        self.scope.shrinkRetainingCapacity(scope_base);

        const loop = try self.store.append(.{ .record = &.{ body, carried, item, source } });
        return self.settledNode(try self.tag("For", &.{ loop, state }), joins.items, state, rest, meta, region);
    }

    /// `while cond { .. }`, carrying the state a `for` carries. The
    /// condition reads it too, because it is what the turn tests.
    fn whileNode(
        self: *Reifier,
        cond_id: CheckedExprId,
        body_id: CheckedExprId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var joins = std.ArrayList(Join).empty;
        defer joins.deinit(self.gpa);
        try self.collectAssigned(&joins, body_id);

        const state = try self.joinMeta(joins.items, region);
        const initials = try self.initialNodes(joins.items, region);
        defer self.gpa.free(initials);

        const scope_base = self.scope.items.len;
        const carried = try self.carriedNodes(joins.items, initials, region);
        const cond = try self.irNode(cond_id);
        const body = try self.loopBodyNode(body_id, joins.items, state, region);
        self.scope.shrinkRetainingCapacity(scope_base);

        const loop = try self.store.append(.{ .record = &.{ body, carried, cond } });
        return self.settledNode(try self.tag("While", &.{ loop, state }), joins.items, state, rest, meta, region);
    }

    /// One turn of a loop, walked with that loop in hand so a `break` or a
    /// `return` inside it has the state and knows it must say the transfer.
    fn loopBodyNode(
        self: *Reifier,
        body_id: CheckedExprId,
        joins: []const Join,
        state: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const outer = self.loop;
        self.loop = .{ .joins = joins, .carried = state };
        defer self.loop = outer;
        return self.joinBranchNode(body_id, .{ .joined = joins }, state, true, region);
    }

    /// One `{ initial, name }` per `var` the loop carries, with the name
    /// bound so the turn reads it.
    ///
    /// Each `var` keeps its own name inside the body, where C28 read the
    /// positions of one tuple, so the turn writes what the author wrote.
    fn carriedNodes(
        self: *Reifier,
        joins: []const Join,
        initials: []const ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const entries = try self.gpa.alloc(ConstNodeId, joins.len);
        defer self.gpa.free(entries);
        for (joins, initials, 0..) |join, initial, index| {
            const name = try self.strNode(try self.nextVersionName(join.binder, region));
            entries[index] = try self.store.append(.{ .record = &.{ initial, name } });
        }
        return self.store.append(.{ .list = .{ .nodes = entries } });
    }

    /// The branches of a join, each handing back the versions it settled.
    fn joinBranches(
        self: *Reifier,
        expr_id: CheckedExprId,
        joins: []const Join,
        carried: ConstNodeId,
        escapes: bool,
        region: base.Region,
    ) Error!ConstNodeId {
        const ending: Ending = .{ .joined = joins };
        const expr = self.bodies.expr(expr_id);
        switch (expr.data) {
            .if_ => |conditional| {
                const values = try self.gpa.alloc(ConstNodeId, conditional.branches.len + 1);
                defer self.gpa.free(values);
                const conds = try self.gpa.alloc(ConstNodeId, conditional.branches.len);
                defer self.gpa.free(conds);

                for (conditional.branches, 0..) |branch, index| {
                    conds[index] = try self.irNode(branch.cond);
                    values[index] = try self.joinBranchNode(branch.body, ending, carried, escapes, region);
                }
                values[conditional.branches.len] =
                    try self.joinBranchNode(conditional.final_else, ending, carried, escapes, region);

                var result = values[conditional.branches.len];
                var index = conditional.branches.len;
                while (index > 0) {
                    index -= 1;
                    result = try self.tag("If", &.{ conds[index], values[index], result, carried });
                }
                return result;
            },
            .match_ => |matched| {
                const subject = try self.irNode(matched.cond);
                var nodes = std.ArrayList(ConstNodeId).empty;
                defer nodes.deinit(self.gpa);
                for (matched.branches) |branch| {
                    const scope_base = self.scope.items.len;
                    defer self.scope.shrinkRetainingCapacity(scope_base);

                    var patterns = std.ArrayList(ConstNodeId).empty;
                    defer patterns.deinit(self.gpa);
                    for (branch.patternsSlice(self.bodies)) |branch_pattern| {
                        try patterns.append(self.gpa, try self.patternNode(branch_pattern.pattern, null));
                    }
                    const pattern_list = try self.store.append(.{ .list = .{ .nodes = patterns.items } });
                    const guard = if (branch.guard) |guard_id|
                        try self.tag("Guard", &.{try self.irNode(guard_id)})
                    else
                        try self.tag("NoGuard", &.{});
                    const value = try self.joinBranchNode(branch.value, ending, carried, escapes, region);
                    try nodes.append(self.gpa, try self.store.append(.{ .record = &.{ guard, pattern_list, value } }));
                }
                const list = try self.store.append(.{ .list = .{ .nodes = nodes.items } });
                return self.tag("Match", &.{ subject, list, carried });
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return self.reject(.unsupported_expression, region, "a statement whose value is discarded"),
        }
    }

    /// One branch of a join. Its own bindings stay inside it, and what it
    /// hands out is the version of each carried `var` it finishes on.
    fn joinBranchNode(
        self: *Reifier,
        body_id: CheckedExprId,
        ending: Ending,
        carried: ConstNodeId,
        escapes: bool,
        region: base.Region,
    ) Error!ConstNodeId {
        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        // A branch of a statement `if` and a loop turn both hand back
        // nothing of their own, so what they end on is either nothing or one
        // more statement wearing the last expression's place.
        var rest: Rest = .{ .statements = &.{}, .ending = ending, .escapes = escapes };
        const final_expr = switch (self.bodies.expr(body_id).data) {
            .block => |block| blk: {
                rest.statements = block.statements;
                break :blk block.final_expr;
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .record,
            .empty_record,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => body_id,
        };
        if (!self.fallsThrough(final_expr)) {
            rest.ending = .{ .trailing = .{ .expr = final_expr, .joins = ending.joined } };
        }
        return self.statementsNode(rest, carried, region);
    }

    /// What a branch hands the join underneath it: the version each carried
    /// `var` is at where the branch ends.
    fn joinedNode(self: *Reifier, joins: []const Join, region: base.Region) Error!ConstNodeId {
        const nodes = try self.initialNodes(joins, region);
        defer self.gpa.free(nodes);
        if (joins.len == 1) return nodes[0];
        const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
        const meta = try self.joinMeta(joins, region);
        // A loop that carries nothing still hands a turn back, and `{}` is
        // what a turn that settles nothing settles.
        if (joins.len == 0) return self.tag("MakeRecord", &.{ list, meta });
        return self.tag("MakeTuple", &.{ list, meta });
    }

    /// Each carried `var` read at the version in scope here.
    fn initialNodes(self: *Reifier, joins: []const Join, region: base.Region) Error![]ConstNodeId {
        const nodes = try self.gpa.alloc(ConstNodeId, joins.len);
        errdefer self.gpa.free(nodes);
        for (joins, 0..) |join, index| {
            const binding = self.lookupBinding(join.binder) orelse
                return self.rejectError(.unsupported_expression, region, "an assignment to a name bound outside this function");
            nodes[index] = try self.tag("Local", &.{ try self.strNode(binding.name), join.meta });
        }
        return nodes;
    }

    /// What one join carries: one `var`'s own type, a tuple of them, or `{}`
    /// where there is no `var` to carry.
    fn joinMeta(self: *Reifier, joins: []const Join, region: base.Region) Error!ConstNodeId {
        if (joins.len == 1) return joins[0].meta;
        const tys = try self.gpa.alloc(ConstNodeId, joins.len);
        defer self.gpa.free(tys);
        for (joins, 0..) |join, index| tys[index] = join.ty;
        const list = try self.store.append(.{ .list = .{ .nodes = tys } });
        if (joins.len == 0) return self.metaNode(try self.tag("Record", &.{list}), region);
        return self.metaNode(try self.tag("Tuple", &.{list}), region);
    }

    /// What a branch that does not transfer contributes, and where the
    /// statements it falls through to are.
    const Fallthrough = union(enum) {
        /// A statement whose value is discarded: the branch hands back
        /// nothing, and the statements after it are what it describes as.
        discarded: Rest,
        /// A binding: the branch's value is the expression the binding was
        /// written with, and the statements after it run under that name.
        bound: struct { name: ConstNodeId, value: CheckedExprId, rest: Rest },
        /// The block's own value: the branch hands back the expression the
        /// transfer was lifted out of, and nothing follows it.
        valued: CheckedExprId,
    };

    /// An `if` or a `match` some branch of which transfers, lifted into the
    /// position the statements after it occupy.
    ///
    /// `if c { return a }` followed by the rest of the body describes as
    /// `If(c, a, rest)`: a branch that returns hands its value back, and a
    /// branch that does not runs the statements written after the `if`.
    /// `h = t?` is the same rewrite around a binding, because the `?`
    /// desugaring is a `match` whose `Err` branch returns and whose `Ok`
    /// branch has the value `h` holds. So is `Ok(t? * 2.0)`, where what the
    /// surviving branch hands back is the whole expression the `?` was
    /// written inside.
    ///
    /// The node takes the block's meta rather than its own: it hands back the
    /// block's value now, where in place it handed back a statement's nothing
    /// or one binding's value.
    fn escapingNode(
        self: *Reifier,
        expr_id: CheckedExprId,
        fell: Fallthrough,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // Built at most once and shared by every branch that falls through to
        // it, because the store holds nodes rather than trees.
        var fallthrough: ?ConstNodeId = null;

        const expr = self.bodies.expr(expr_id);
        switch (expr.data) {
            .if_ => |conditional| {
                const values = try self.gpa.alloc(ConstNodeId, conditional.branches.len + 1);
                defer self.gpa.free(values);
                const conds = try self.gpa.alloc(ConstNodeId, conditional.branches.len);
                defer self.gpa.free(conds);

                for (conditional.branches, 0..) |branch, index| {
                    conds[index] = try self.irNode(branch.cond);
                    values[index] = try self.escapingBranchNode(branch.body, expr_id, fell, &fallthrough, meta, region);
                }
                values[conditional.branches.len] =
                    try self.escapingBranchNode(conditional.final_else, expr_id, fell, &fallthrough, meta, region);

                var result = values[conditional.branches.len];
                var index = conditional.branches.len;
                while (index > 0) {
                    index -= 1;
                    result = try self.tag("If", &.{ conds[index], values[index], result, meta });
                }
                return result;
            },
            .match_ => |matched| {
                const subject = try self.irNode(matched.cond);
                var nodes = std.ArrayList(ConstNodeId).empty;
                defer nodes.deinit(self.gpa);
                for (matched.branches) |branch| {
                    try nodes.append(self.gpa, try self.escapingMatchBranchNode(branch, expr_id, fell, &fallthrough, meta, region));
                }
                const list = try self.store.append(.{ .list = .{ .nodes = nodes.items } });
                return self.tag("Match", &.{ subject, list, meta });
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => return self.reject(.unsupported_expression, region, "a statement whose value is discarded"),
        }
    }

    /// One branch: what it transfers, or the statements it falls through to,
    /// under the binding it fills where one was written.
    fn escapingBranchNode(
        self: *Reifier,
        body_id: CheckedExprId,
        lifted: CheckedExprId,
        fell: Fallthrough,
        fallthrough: *?ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (self.escapesEarly(body_id)) return self.tailNode(body_id, meta);

        switch (fell) {
            .discarded => |rest| {
                if (!self.fallsThrough(body_id)) {
                    return self.reject(.unsupported_expression, region, "a statement whose value is discarded");
                }
                return self.fallthroughNode(rest, fallthrough, meta, region);
            },
            .bound => |binding| {
                const value = try self.substitutedNode(binding.value, lifted, body_id, region);
                const under = try self.fallthroughNode(binding.rest, fallthrough, meta, region);
                return self.tag("Let", &.{ binding.name, value, under, meta });
            },
            .valued => |value_id| return self.substitutedNode(value_id, lifted, body_id, region),
        }
    }

    /// The statements after the lifted construct, described once and shared
    /// by every branch that falls through to them.
    fn fallthroughNode(
        self: *Reifier,
        rest: Rest,
        fallthrough: *?ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (fallthrough.*) |node| return node;
        const node = try self.statementsNode(rest, meta, region);
        fallthrough.* = node;
        return node;
    }

    /// The expression a transfer was lifted out of, described with this
    /// branch's value standing where the lifted construct was written.
    ///
    /// The two coincide where the construct was the whole expression, which
    /// is the shape a statement `if` and a plain `h = t?` both have.
    fn substitutedNode(
        self: *Reifier,
        expr_id: CheckedExprId,
        lifted: CheckedExprId,
        body_id: CheckedExprId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (expr_id == lifted) return self.irNode(body_id);

        try self.lifts.append(self.gpa, .{ .expr = lifted, .node = try self.irNode(body_id) });
        defer _ = self.lifts.pop();

        const expr = self.bodies.expr(expr_id);
        const meta = try self.metaNode(try self.tyNode(expr.ty, expr.source_region), expr.source_region);
        return self.valueNode(expr_id, meta, region);
    }

    /// One `match` branch. The names its pattern binds are in scope for the
    /// value it hands back, and a branch that falls through binds none the
    /// statements after it can read.
    fn escapingMatchBranchNode(
        self: *Reifier,
        branch: checked.CheckedMatchBranch,
        lifted: CheckedExprId,
        fell: Fallthrough,
        fallthrough: *?ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        var nodes = std.ArrayList(ConstNodeId).empty;
        defer nodes.deinit(self.gpa);
        for (branch.patternsSlice(self.bodies)) |branch_pattern| {
            try nodes.append(self.gpa, try self.patternNode(branch_pattern.pattern, null));
        }
        const patterns = try self.store.append(.{ .list = .{ .nodes = nodes.items } });

        const guard = if (branch.guard) |guard_id|
            try self.tag("Guard", &.{try self.irNode(guard_id)})
        else
            try self.tag("NoGuard", &.{});

        const value = try self.escapingBranchNode(branch.value, lifted, fell, fallthrough, meta, region);
        return self.store.append(.{ .record = &.{ guard, patterns, value } });
    }

    /// The construct a transfer written inside this expression is lifted out
    /// past: this expression when a branch of it transfers, and otherwise the
    /// first one under it that does.
    ///
    /// `Ok(t? * 2.0)` holds the `match` the `?` desugars to, and lifting that
    /// out leaves `Match(t, [Ok(v) => Ok(v times 2.0), Err(e) => Err(e)])`,
    /// which has no transfer left in it. The walk does it once here rather
    /// than every translator doing it for itself.
    fn liftable(self: *Reifier, expr_id: CheckedExprId) ?CheckedExprId {
        for (self.lifts.items) |lift| {
            if (lift.expr == expr_id) return null;
        }
        if (self.branchesEscape(expr_id)) return expr_id;

        return switch (self.bodies.expr(expr_id).data) {
            .binop => |binop| self.liftable(binop.lhs) orelse self.liftable(binop.rhs),
            .unary_minus, .unary_not => |operand| self.liftable(operand),
            .tuple, .list, .str => |items| self.liftableOf(items),
            .tag => |built| self.liftableOf(built.args),
            .call => |call| self.liftable(call.func) orelse self.liftableOf(call.args),
            .field_access => |access| self.liftable(access.receiver),
            .tuple_access => |access| self.liftable(access.tuple),
            .nominal => |nominal| self.liftable(nominal.backing_expr),
            .row_coerce => |coerce| self.liftable(coerce.value),
            .structural_eq => |eq| self.liftable(eq.lhs) orelse self.liftable(eq.rhs),
            .record => |record| blk: {
                for (record.fields) |field| {
                    if (self.liftable(field.value)) |found| break :blk found;
                }
                break :blk if (record.ext) |ext| self.liftable(ext) else null;
            },
            .dispatch_call, .method_eq, .type_dispatch_call => |plan_id| self.liftableDispatch(plan_id),
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .empty_list,
            .match_,
            .if_,
            .empty_record,
            .block,
            .zero_argument_tag,
            .closure,
            .lambda,
            .interpolation,
            .structural_hash,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => null,
        };
    }

    fn liftableOf(self: *Reifier, exprs: []const CheckedExprId) ?CheckedExprId {
        for (exprs) |expr_id| {
            if (self.liftable(expr_id)) |found| return found;
        }
        return null;
    }

    /// A dispatch's operands, which is where `t?.sin()` and `a? + b?` both
    /// put the construct to lift.
    fn liftableDispatch(self: *Reifier, plan_id: ?static_dispatch.StaticDispatchPlanId) ?CheckedExprId {
        const id = plan_id orelse return null;
        const plan = self.plans.plans[@backingInt(id)];
        for (plan.argsSlice(self.plans)) |operand| {
            switch (operand) {
                .checked_expr => |child| if (self.liftable(child)) |found| return found,
                .generated_interpolation_segments, .generated_numeral, .generated_quote => {},
            }
        }
        return null;
    }

    /// Whether some branch of this expression transfers, which is what makes
    /// it the construct a lift takes out.
    fn branchesEscape(self: *Reifier, expr_id: CheckedExprId) bool {
        return switch (self.bodies.expr(expr_id).data) {
            .if_ => |conditional| blk: {
                for (conditional.branches) |branch| {
                    if (self.escapesEarly(branch.body)) break :blk true;
                }
                break :blk self.escapesEarly(conditional.final_else);
            },
            .match_ => |matched| blk: {
                for (matched.branches) |branch| {
                    if (self.escapesEarly(branch.value)) break :blk true;
                }
                break :blk false;
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .block,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => false,
        };
    }

    /// Whether every path through this expression transfers control, so the
    /// branch it stands in is the transfer and nothing else.
    fn escapesEarly(self: *Reifier, expr_id: CheckedExprId) bool {
        return switch (self.bodies.expr(expr_id).data) {
            .return_, .break_ => true,
            // A widening whose value never arrives never arrives either.
            .row_coerce => |coerce| self.escapesEarly(coerce.value),
            .block => |block| blk: {
                for (block.statements) |statement_id| {
                    switch (self.bodies.statement(statement_id).data) {
                        .return_, .break_ => break :blk true,
                        .pending,
                        .decl,
                        .promoted_proc,
                        .var_,
                        .var_uninitialized,
                        .reassign,
                        .crash,
                        .dbg,
                        .expr,
                        .expect,
                        .for_,
                        .while_,
                        .infinite_loop,
                        .breakable_loop,
                        .import_,
                        .alias_decl,
                        .where_alias_decl,
                        .nominal_decl,
                        .type_anno,
                        .type_var_alias,
                        .runtime_error,
                        => {},
                    }
                }
                break :blk self.escapesEarly(block.final_expr);
            },
            .if_ => |conditional| blk: {
                for (conditional.branches) |branch| {
                    if (!self.escapesEarly(branch.body)) break :blk false;
                }
                break :blk self.escapesEarly(conditional.final_else);
            },
            .match_ => |matched| blk: {
                for (matched.branches) |branch| {
                    if (!self.escapesEarly(branch.value)) break :blk false;
                }
                break :blk matched.branches.len != 0;
            },
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .call,
            .record,
            .empty_record,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => false,
        };
    }

    /// Whether this expression does nothing and hands back nothing, which is
    /// what the branch an `if` was written without stands for.
    fn fallsThrough(self: *Reifier, expr_id: CheckedExprId) bool {
        return switch (self.bodies.expr(expr_id).data) {
            .empty_record => true,
            .record => |record| record.fields.len == 0 and record.ext == null,
            .block => |block| block.statements.len == 0 and self.fallsThrough(block.final_expr),
            .pending,
            .numeral,
            .str_from_quote,
            .code_from_lambda,
            .str_segment,
            .str,
            .row_coerce,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
            .list,
            .empty_list,
            .tuple,
            .match_,
            .if_,
            .call,
            .tag,
            .nominal,
            .zero_argument_tag,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
            .unary_not,
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
            .runtime_error,
            .crash,
            .dbg,
            .expect_err,
            .expect,
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .for_,
            .hosted_lambda,
            .run_low_level,
            => false,
        };
    }

    /// One binding, and the statements that run under it.
    fn declNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        value_id: CheckedExprId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // The `Ir` is first order, so a binding that holds a function is
        // held rather than bound and leaves no `Let` behind: a lambda written
        // here becomes a row of its own, and one a call handed back folds
        // into the call that runs it.
        if (self.functionOf(self.bodies.expr(value_id).ty) != null) {
            _ = try self.bind(pattern_id, .{ .function = value_id }, region);
            return self.statementsNode(rest, meta, region);
        }

        // `_ = e` names nothing, so it is the discarded statement it is: a
        // binding nothing reads, which keeps both its order and whatever it
        // diverges on.
        if (self.bodies.pattern(pattern_id).data == .underscore) {
            return self.discardedNode(value_id, rest, meta, region);
        }

        if (self.bodies.pattern(pattern_id).data != .assign) {
            return self.destructuringNode(pattern_id, value_id, rest, meta, region);
        }

        // A value whose branches return early is lifted around the binding:
        // `h = t?` is a `match` whose `Err` branch returns, so the `match`
        // goes outside and the binding goes inside the branch that has a
        // value to bind. The name is bound first, because the statements
        // under the binding read it.
        const name = try self.strNode(try self.bindLocal(pattern_id, region));
        if (rest.escapes) {
            if (self.liftable(value_id)) |lifted| {
                const fell: Fallthrough = .{ .bound = .{ .name = name, .value = value_id, .rest = rest } };
                return self.escapingNode(lifted, fell, meta, region);
            }
        }

        const value = try self.irNode(value_id);
        const under = try self.statementsNode(rest, meta, region);
        return self.tag("Let", &.{ name, value, under, meta });
    }

    /// An assignment to a `var`, described as a new version of the name.
    ///
    /// The `Ir` has no assignment and should not gain one: a translator
    /// emitting SQL has no store to write to. So each assignment binds a
    /// name of its own, `x` then `x#1` then `x#2`, and a read resolves to the
    /// version in scope where it stands. A version nothing reads leaves a
    /// `Let` nothing reads, which is what the source said.
    fn reassignNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        value_id: CheckedExprId,
        reassigned: []const checked.PatternBinderId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        // Described before the new version enters scope, because `x = x + 1`
        // reads the version it replaces.
        const value = try self.irNode(value_id);
        const name = try self.strNode(try self.bindVersion(pattern_id, reassigned, region));
        const under = try self.statementsNode(rest, meta, region);
        return self.tag("Let", &.{ name, value, under, meta });
    }

    /// The name one assignment binds: the `var`'s own spelling with the
    /// number of assignments before it, counted over the versions in scope.
    fn bindVersion(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        reassigned: []const checked.PatternBinderId,
        region: base.Region,
    ) Error![]const u8 {
        if (reassigned.len != 1) {
            return self.rejectError(.unsupported_expression, region, "an assignment that writes more than one name");
        }
        const binder = reassigned[0];
        const name = try self.nextVersionName(binder, region);

        // A read after the assignment resolves to whichever of the two
        // binders the checker recorded, so both carry the latest version.
        if (self.bodies.patternBinderForCheckedPattern(pattern_id)) |written_binder| {
            if (written_binder != binder) {
                try self.scope.append(self.gpa, .{ .binder = written_binder, .name = name, .kind = .local });
            }
        }
        return name;
    }

    /// The next version of one `var`: its own spelling with the number of
    /// versions already in scope, which puts `$x` before `$x#1` before
    /// `$x#2`. The version enters scope here, so a read after it finds it.
    fn nextVersionName(
        self: *Reifier,
        binder: checked.PatternBinderId,
        region: base.Region,
    ) Error![]const u8 {
        if (self.lookupBinding(binder) == null) {
            return self.rejectError(.unsupported_expression, region, "an assignment to a name bound outside this function");
        }

        const seen = try self.var_versions.getOrPut(self.gpa, binder);
        if (!seen.found_existing) seen.value_ptr.* = 0;
        seen.value_ptr.* += 1;
        const versions = seen.value_ptr.*;

        const written = self.binderName(binder);
        const spelling = if (isWrittenName(written)) written else try self.inventedName();
        const name = try std.fmt.allocPrint(self.gpa, "{s}#{d}", .{ spelling, versions });
        errdefer self.gpa.free(name);
        try self.invented_names.append(self.gpa, name);

        try self.scope.append(self.gpa, .{ .binder = binder, .name = name, .kind = .local });
        return name;
    }

    /// One wrapper a destructuring binding puts around the statements beneath
    /// it.
    const Destructure = union(enum) {
        /// A name, and what it reads out of the value.
        bound: struct { name: ConstNodeId, value: ConstNodeId },
        /// A value, and the pattern that names the variant it holds.
        tested: struct { subject: ConstNodeId, pattern: ConstNodeId },
    };

    /// A binding whose pattern takes the value apart, expanded into the reads
    /// it stands for: `{ a, b } = r` binds `a` to `r.a` and `b` to `r.b`, and
    /// `(a, b) = t` binds the two positions of `t`.
    ///
    /// Reads rather than a one-branch `Match`, because a record and a tuple
    /// are taken apart by reading them and a translator with no pattern
    /// matching can emit that. Only a pattern that names a variant needs a
    /// `Match`, and that one gets the single branch it is.
    fn destructuringNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        value_id: CheckedExprId,
        rest: Rest,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var steps = std.ArrayList(Destructure).empty;
        defer steps.deinit(self.gpa);

        const value = try self.irNode(value_id);
        try self.destructureInto(&steps, pattern_id, value, self.readsAName(value_id), region);

        // The names are in scope now, so the statements under the binding are
        // described before the wrappers go on outside in.
        return self.wrapDestructures(steps.items, try self.statementsNode(rest, meta, region), meta);
    }

    /// Put the reads one or more patterns stand for around the node that reads
    /// the names they bind, the first read outermost.
    fn wrapDestructures(
        self: *Reifier,
        steps: []const Destructure,
        inner: ConstNodeId,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        var node = inner;
        var index = steps.len;
        while (index > 0) {
            index -= 1;
            node = switch (steps[index]) {
                .bound => |binding| try self.tag("Let", &.{ binding.name, binding.value, node, meta }),
                .tested => |test_| blk: {
                    const patterns = try self.store.append(.{ .list = .{ .nodes = &.{test_.pattern} } });
                    const guard = try self.tag("NoGuard", &.{});
                    const branch = try self.store.append(.{ .record = &.{ guard, patterns, node } });
                    const branches = try self.store.append(.{ .list = .{ .nodes = &.{branch} } });
                    break :blk try self.tag("Match", &.{ test_.subject, branches, meta });
                },
            };
        }
        return node;
    }

    /// The reads one pattern stands for, in the order its names enter scope.
    fn destructureInto(
        self: *Reifier,
        steps: *std.ArrayList(Destructure),
        pattern_id: CheckedPatternId,
        subject: ConstNodeId,
        subject_reads_a_name: bool,
        region: base.Region,
    ) Error!void {
        const pattern = self.bodies.pattern(pattern_id);
        switch (pattern.data) {
            // `_` names nothing, so there is nothing to read.
            .underscore => {},
            .assign => {
                const name = try self.strNode(try self.bindLocal(pattern_id, region));
                try steps.append(self.gpa, .{ .bound = .{ .name = name, .value = subject } });
            },
            // `p as name` binds the whole value, and the pattern beside it
            // reads that name rather than the value a second time.
            .as => |renamed| {
                const name = try self.strNode(try self.bindBinder(renamed.binder, .local));
                try steps.append(self.gpa, .{ .bound = .{ .name = name, .value = subject } });
                const read = try self.tag("Local", &.{ name, try self.patternMeta(pattern_id) });
                try self.destructureInto(steps, renamed.pattern, read, true, region);
            },
            .record_destructure => |destructs| {
                var reads: usize = 0;
                for (destructs) |destruct| {
                    if (destruct.kind != .rest) reads += 1;
                }
                const read = try self.sharedSubject(steps, pattern_id, subject, subject_reads_a_name, reads);
                for (destructs) |destruct| {
                    const field_pattern = switch (destruct.kind) {
                        .required, .sub_pattern => |inner| inner,
                        // A `..` that binds nothing stands for the fields the
                        // pattern did not name, and naming none of them is
                        // what reading only the named ones says. One that
                        // binds a name binds a record built out of what is
                        // left, which is not a read.
                        .rest => |inner| {
                            if (self.bodies.pattern(inner).data == .underscore) continue;
                            return self.rejectError(.unsupported_expression, region, "a record pattern whose `..` binds a name");
                        },
                    };
                    const name = try self.strNode(self.names.recordFieldLabelText(destruct.label));
                    const field_meta = try self.patternMeta(field_pattern);
                    const field = try self.tag("Field", &.{ read, name, field_meta });
                    try self.destructureInto(steps, field_pattern, field, false, region);
                }
            },
            .tuple => |items| {
                var reads: usize = 0;
                for (items) |item| {
                    if (self.bodies.pattern(item).data != .underscore) reads += 1;
                }
                const read = try self.sharedSubject(steps, pattern_id, subject, subject_reads_a_name, reads);
                for (items, 0..) |item, position| {
                    if (self.bodies.pattern(item).data == .underscore) continue;
                    const index = try self.store.append(.{ .scalar = .{ .u64 = @intCast(position) } });
                    const item_meta = try self.patternMeta(item);
                    const read_item = try self.tag("Index", &.{ read, index, item_meta });
                    try self.destructureInto(steps, item, read_item, false, region);
                }
            },
            // A pattern that names a variant is a test as well as a binding,
            // so it stays the `match` it is.
            .applied_tag, .nominal => {
                const node = try self.patternNode(pattern_id, null);
                try steps.append(self.gpa, .{ .tested = .{ .subject = subject, .pattern = node } });
            },
            .list,
            .numeral_literal,
            .str_literal,
            .str_interpolation,
            .pending,
            .runtime_error,
            => return self.rejectError(.unsupported_expression, region, patternFormName(pattern.data)),
        }
    }

    /// A read of a value that a pattern takes apart more than one way.
    ///
    /// Each name the pattern binds reads the value again, so the value is
    /// bound once first. One that already reads a name is read again instead:
    /// the name is the translator's to repeat, and a `Let` around it would
    /// say nothing. This is the rule a record update follows, for the reason
    /// it follows it.
    fn sharedSubject(
        self: *Reifier,
        steps: *std.ArrayList(Destructure),
        pattern_id: CheckedPatternId,
        subject: ConstNodeId,
        reads_a_name: bool,
        reads: usize,
    ) Error!ConstNodeId {
        if (reads_a_name or reads < 2) return subject;
        const meta = try self.patternMeta(pattern_id);
        const name = try self.strNode(try self.inventedName());
        try steps.append(self.gpa, .{ .bound = .{ .name = name, .value = subject } });
        return self.tag("Local", &.{ name, meta });
    }

    /// What the checker knew about one pattern: the type it solved for it,
    /// and where it was written.
    fn patternMeta(self: *Reifier, pattern_id: CheckedPatternId) Error!ConstNodeId {
        const pattern = self.bodies.pattern(pattern_id);
        const ty = try self.tyNode(pattern.ty, pattern.source_region);
        return self.metaNode(ty, pattern.source_region);
    }

    /// `tail` says the `if` hands its value back as the reified function's,
    /// which is what lets a branch be written as a `return`.
    fn ifNode(
        self: *Reifier,
        branches: []const checked.CheckedIfBranch,
        final_else: CheckedExprId,
        escapes: bool,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        var result = if (escapes) try self.tailNode(final_else, meta) else try self.irNode(final_else);
        var index = branches.len;
        while (index > 0) {
            index -= 1;
            const cond = try self.irNode(branches[index].cond);
            const then = if (escapes)
                try self.tailNode(branches[index].body, meta)
            else
                try self.irNode(branches[index].body);
            result = try self.tag("If", &.{ cond, then, result, meta });
        }
        return result;
    }

    /// A tag: a Bool literal, or a variant of a tag union.
    ///
    /// Bool is the one tag union with a `Lit`, because a translator emitting a
    /// boolean wants the value rather than the two tags Roc represents it
    /// with. Every other union describes as the construction it is.
    fn tagNode(
        self: *Reifier,
        name: canonical.TagLabelId,
        args: []const CheckedExprId,
        subject_ty: CheckedTypeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (self.primitiveOf(subject_ty) == .bool) {
            const flag = self.bool_tags.value(name) orelse
                return self.reject(.unsupported_expression, region, "a tag");
            return self.boolLiteralNode(flag, meta);
        }

        const payloads = try self.irNodes(args);
        defer self.gpa.free(payloads);
        const list = try self.store.append(.{ .list = .{ .nodes = payloads } });
        const label = try self.strNode(self.names.tagLabelText(name));
        return self.tag("MakeTag", &.{ label, list, meta });
    }

    /// A `match`, with its branches in the order they were written.
    ///
    /// The names a branch's patterns bind are in scope for that branch's guard
    /// and value and nowhere else, so each branch takes the staged scope back
    /// to where it found it.
    fn matchNode(
        self: *Reifier,
        cond_id: CheckedExprId,
        branches: []const checked.CheckedMatchBranch,
        escapes: bool,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        const subject = try self.irNode(cond_id);

        var nodes = std.ArrayList(ConstNodeId).empty;
        defer nodes.deinit(self.gpa);
        for (branches) |branch| {
            try nodes.append(self.gpa, try self.branchNode(branch, escapes, meta));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = nodes.items } });
        return self.tag("Match", &.{ subject, list, meta });
    }

    /// One `{ guard, patterns, value }` branch.
    ///
    /// A branch written `A | B =>` carries a pattern per alternative, and every
    /// alternative binds the same names, so the walk binds all of them and the
    /// value reads whichever binder the checker gave it.
    fn branchNode(
        self: *Reifier,
        branch: checked.CheckedMatchBranch,
        escapes: bool,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        var nodes = std.ArrayList(ConstNodeId).empty;
        defer nodes.deinit(self.gpa);
        for (branch.patternsSlice(self.bodies)) |branch_pattern| {
            try nodes.append(self.gpa, try self.patternNode(branch_pattern.pattern, null));
        }
        const patterns = try self.store.append(.{ .list = .{ .nodes = nodes.items } });

        const guard = if (branch.guard) |guard_id|
            try self.tag("Guard", &.{try self.irNode(guard_id)})
        else
            try self.tag("NoGuard", &.{});

        const value = if (escapes) try self.tailNode(branch.value, meta) else try self.irNode(branch.value);

        // A constant record's fields are restored in label order, not in the
        // order the type declares them.
        return self.store.append(.{ .record = &.{ guard, patterns, value } });
    }

    /// One pattern. `ty_override` plays the part it plays in `irNodeAs`: a
    /// nominal hands its own type down to the pattern matching its backing.
    fn patternNode(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        ty_override: ?TypeOverride,
    ) Error!ConstNodeId {
        const pattern = self.bodies.pattern(pattern_id);
        const region = pattern.source_region;
        const subject_ty = if (ty_override) |override| override.checked else pattern.ty;
        const ty = if (ty_override) |override| override.node else try self.tyNode(pattern.ty, region);
        const meta = try self.metaNode(ty, region);

        return switch (pattern.data) {
            .assign => blk: {
                const name = try self.strNode(try self.bindLocal(pattern_id, region));
                break :blk try self.tag("Bind", &.{ name, meta });
            },
            .underscore => try self.tag("Anything", &.{meta}),
            .applied_tag => |applied| try self.variantPattern(applied.name, applied.args, subject_ty, meta, region),
            .nominal => |nominal| try self.patternNode(
                nominal.backing_pattern,
                .{ .node = ty, .checked = subject_ty },
            ),
            .tuple => |items| blk: {
                const nodes = try self.patternNodes(items);
                defer self.gpa.free(nodes);
                const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
                break :blk try self.tag("PatTuple", &.{ list, meta });
            },
            .record_destructure => |destructs| try self.recordPattern(destructs, meta, region),
            .numeral_literal => |numeral_pattern| blk: {
                if (numeral_pattern.guard) |guard| {
                    break :blk try self.guardedLiteralPattern(pattern_id, guard, meta);
                }
                const primitive = self.primitiveOf(pattern.ty) orelse
                    break :blk try self.reject(.unresolved_type, region, "this numeric literal");
                const lit = try self.numeralLit(numeral_pattern.literal, primitive, ty, region);
                break :blk try self.tag("PatLit", &.{ lit, meta });
            },
            .str_literal => |str_pattern| blk: {
                if (str_pattern.guard) |guard| {
                    break :blk try self.guardedLiteralPattern(pattern_id, guard, meta);
                }
                const text = try self.strNode(self.bodies.stringLiteral(str_pattern.literal));
                const lit = try self.tag("Str", &.{text});
                break :blk try self.tag("PatLit", &.{ lit, meta });
            },
            // The name is bound beside the pattern rather than rewritten into
            // the branch body: the author wrote it in the pattern, and a
            // target with its own `as` has to find it there.
            .as => |renamed| blk: {
                const inner = try self.patternNode(renamed.pattern, ty_override);
                const name = try self.strNode(try self.bindBinder(renamed.binder, .local));
                break :blk try self.tag("PatAs", &.{ inner, name, meta });
            },
            .list => |list_pattern| try self.listPattern(list_pattern.patterns, list_pattern.rest, meta, region),
            .str_interpolation => |str_pattern| try self.strPattern(
                str_pattern.prefix,
                str_pattern.steps,
                str_pattern.end,
                meta,
            ),
            .pending,
            .runtime_error,
            => try self.reject(.unsupported_expression, region, patternFormName(pattern.data)),
        };
    }

    /// A tag pattern: a Bool literal, or a variant of a tag union. The split
    /// is the one `tagNode` makes, so a Bool reads the same in a pattern as it
    /// does in an expression.
    fn variantPattern(
        self: *Reifier,
        name: canonical.TagLabelId,
        args: []const CheckedPatternId,
        subject_ty: CheckedTypeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (self.primitiveOf(subject_ty) == .bool) {
            const flag = self.bool_tags.value(name) orelse
                return self.reject(.unsupported_expression, region, "a tag pattern");
            const lit = try self.tag("Bool", &.{try self.tag(if (flag) "True" else "False", &.{})});
            return self.tag("PatLit", &.{ lit, meta });
        }

        const nodes = try self.patternNodes(args);
        defer self.gpa.free(nodes);
        const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
        const label = try self.strNode(self.names.tagLabelText(name));
        return self.tag("Variant", &.{ label, list, meta });
    }

    /// A literal pattern of the author's own type: the value bound, and the
    /// author's equality against the author's conversion of the literal.
    ///
    /// The checker writes both halves. The pattern carries a binder of its
    /// own, and the condition beside it reads that binder, which is why the
    /// binder goes into scope before the condition is described.
    ///
    /// The condition stays on the pattern rather than moving to the branch.
    /// A branch's guard is tested once some alternative matched without
    /// saying which, so `Ok(380) | Err(_)` has nowhere to put a condition
    /// that holds for the first alternative and reads a name only it binds.
    fn guardedLiteralPattern(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        guard: CheckedExprId,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse
            return self.reject(
                .unsupported_expression,
                self.bodies.pattern(pattern_id).source_region,
                "a literal pattern the checker left without a binder",
            );
        const name = try self.strNode(try self.bindBinder(binder, .local));
        const bound = try self.tag("Bind", &.{ name, meta });
        return self.tag("PatGuard", &.{ bound, try self.irNode(guard), meta });
    }

    /// A record pattern, one entry per field it names.
    fn recordPattern(
        self: *Reifier,
        destructs: []const checked.CheckedRecordDestruct,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var entries = std.ArrayList(ConstNodeId).empty;
        defer entries.deinit(self.gpa);

        for (destructs) |destruct| {
            const field_pattern = switch (destruct.kind) {
                .required, .sub_pattern => |inner| inner,
                .rest => |inner| {
                    // A `..` that binds nothing is already described by the
                    // entries beside it: it stands for the fields the pattern
                    // did not name, and naming none of them is what those
                    // entries say.
                    if (self.bodies.pattern(inner).data == .underscore) continue;
                    // One that binds a name binds a record the pattern builds
                    // out of the fields left over, and `Pattern` names values
                    // a match takes apart.
                    return self.reject(.unsupported_expression, region, "a record pattern whose `..` binds a name");
                },
            };
            const name = try self.strNode(self.names.recordFieldLabelText(destruct.label));
            const node = try self.patternNode(field_pattern, null);
            try entries.append(self.gpa, try self.store.append(.{ .record = &.{ name, node } }));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = entries.items } });
        return self.tag("PatRecord", &.{ list, meta });
    }

    /// A list pattern, in whichever of the two shapes it was written.
    ///
    /// `[p, q]` asks whether the list holds exactly these and `[p, .., q]`
    /// whether it holds at least these, so they are two nodes rather than one
    /// carrying an optional rest: a translator answers the first with a test
    /// on the length and the second with a slice.
    ///
    /// The rest is not one of the patterns the checker holds. Its index says
    /// where it stood among them, so the patterns split there into the ones
    /// written before it and the ones written after.
    fn listPattern(
        self: *Reifier,
        patterns: []const CheckedPatternId,
        rest: ?checked.CheckedListRestPattern,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const found = rest orelse {
            const nodes = try self.patternNodes(patterns);
            defer self.gpa.free(nodes);
            const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
            return self.tag("PatList", &.{ list, meta });
        };
        if (found.index > patterns.len) {
            return self.reject(.unsupported_expression, region, "a list pattern whose rest stands outside it");
        }

        // The names go into scope in the order they were written, which is
        // the order a guard beside them and the branch value read them in.
        const before = try self.patternNodes(patterns[0..found.index]);
        defer self.gpa.free(before);
        const binding = try self.restBinding(found.pattern);
        const after = try self.patternNodes(patterns[found.index..]);
        defer self.gpa.free(after);

        const head = try self.store.append(.{ .list = .{ .nodes = before } });
        const tail = try self.store.append(.{ .list = .{ .nodes = after } });
        return self.tag("PatListRest", &.{ head, binding, tail, meta });
    }

    /// A string interpolation pattern, transcribed.
    ///
    /// The compiler holds one as the text the string starts with and one step
    /// per interpolation, each the slice that step captures and the delimiter
    /// that ends it. `Exact` says the last delimiter ends the string, and
    /// `Tail` says the last capture takes whatever is left.
    ///
    /// A target that cannot split a string rejects this node by name. That
    /// costs one translator a rejection, where refusing the pattern here
    /// would cost every author the construct.
    fn strPattern(
        self: *Reifier,
        prefix: checked.CheckedStringLiteralId,
        steps: []const checked.CheckedStrPatternStep,
        end: checked.CheckedStrPatternEnd,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        var nodes = std.ArrayList(ConstNodeId).empty;
        defer nodes.deinit(self.gpa);
        for (steps) |step| {
            const capture = try self.restBinding(step.capture);
            const delimiter = try self.strNode(self.bodies.stringLiteral(step.delimiter));
            try nodes.append(self.gpa, try self.store.append(.{ .record = &.{ capture, delimiter } }));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = nodes.items } });
        const head = try self.strNode(self.bodies.stringLiteral(prefix));
        const ending = try self.tag(switch (end) {
            .exact => "Exact",
            .tail => "Tail",
        }, &.{});
        return self.tag("PatStr", &.{ head, list, ending, meta });
    }

    /// What a pattern binds where it may bind only a name: the name, or
    /// nothing. A list's rest and a string pattern's capture both take this
    /// shape, so both read it here.
    fn restBinding(self: *Reifier, pattern_id: ?CheckedPatternId) Error!ConstNodeId {
        const bound = pattern_id orelse return self.tag("Ignored", &.{});
        const pattern = self.bodies.pattern(bound);
        if (pattern.data == .underscore) return self.tag("Ignored", &.{});
        const name = try self.bindLocal(bound, pattern.source_region);
        return self.tag("Named", &.{try self.strNode(name)});
    }

    fn patternNodes(self: *Reifier, ids: []const CheckedPatternId) Error![]ConstNodeId {
        const nodes = try self.gpa.alloc(ConstNodeId, ids.len);
        errdefer self.gpa.free(nodes);
        for (ids, 0..) |id, index| nodes[index] = try self.patternNode(id, null);
        return nodes;
    }

    /// A record literal, and a record update as the literal it stands for.
    ///
    /// A field the literal deliberately leaves unset (`b: _`) is left out of
    /// the entries: `MakeRecord` lists what the literal sets, and the type
    /// beside it says which fields may be absent, so `{ a: v, b: _ }` and
    /// `{ a: v }` describe alike because they build the same value.
    fn recordNode(
        self: *Reifier,
        fields: []const checked.CheckedRecordExprField,
        ext: ?CheckedExprId,
        subject_ty: CheckedTypeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        if (ext) |subject| return self.recordUpdateNode(subject, fields, subject_ty, meta, region);

        const entries = try self.gpa.alloc(ConstNodeId, fields.len);
        defer self.gpa.free(entries);
        for (fields, 0..) |field, index| {
            const name = try self.strNode(self.names.recordFieldLabelText(field.label));
            const value = try self.irNode(field.value);
            entries[index] = try self.store.append(.{ .record = &.{ name, value } });
        }
        const list = try self.store.append(.{ .list = .{ .nodes = entries } });
        return self.tag("MakeRecord", &.{ list, meta });
    }

    /// A record update: the record it builds, field by field.
    ///
    /// `{ ..r, b: 1 }` gets no node of its own. Every field of the result is
    /// either one the update wrote or one read out of `r`, and the record
    /// type is closed by the time the walk sees it, so the whole set is
    /// known. An `UpdateRecord` node would instead hand every translator a
    /// case that GLSL and SQL have no form for, which is the case C17
    /// rejected for `Apply` and for the same reason.
    ///
    /// The subject is read once per field the update did not write, so it is
    /// bound first and the fields read the binding. A subject that already
    /// reads a name is read again instead: the name is the translator's to
    /// repeat, and a `Let` around it would say nothing.
    fn recordUpdateNode(
        self: *Reifier,
        subject_id: CheckedExprId,
        written: []const checked.CheckedRecordExprField,
        subject_ty: CheckedTypeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var declared = std.ArrayList(FieldRef).empty;
        defer declared.deinit(self.gpa);
        try self.updatedRecordFields(&declared, subject_ty, region);

        const subject_expr = self.bodies.expr(subject_id);
        const subject = try self.irNode(subject_id);
        const subject_ty_node = try self.tyNode(subject_expr.ty, subject_expr.source_region);
        const subject_meta = try self.metaNode(subject_ty_node, subject_expr.source_region);

        // A read of the subject, which is the bound name where one was
        // invented and the subject's own description where none was.
        var binding: ?[]const u8 = null;
        var read = subject;
        if (!self.readsAName(subject_id)) {
            const name = try self.inventedName();
            binding = name;
            read = try self.tag("Local", &.{ try self.strNode(name), subject_meta });
        }

        var entries = std.ArrayList(ConstNodeId).empty;
        defer entries.deinit(self.gpa);
        for (declared.items) |field| {
            const label = field.reader.names.recordFieldLabelText(field.field.name);
            const name = try self.strNode(label);
            const value = if (self.writtenField(written, field)) |value_id|
                try self.irNode(value_id)
            else value: {
                const field_ty = try field.reader.tyNode(field.field.ty, region);
                const field_meta = try self.metaNode(field_ty, region);
                break :value try self.tag("Field", &.{ read, name, field_meta });
            };
            try entries.append(self.gpa, try self.store.append(.{ .record = &.{ name, value } }));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = entries.items } });
        const built = try self.tag("MakeRecord", &.{ list, meta });
        const name = binding orelse return built;
        return self.tag("Let", &.{ try self.strNode(name), subject, built, meta });
    }

    /// What one record update wrote for a field, or null where it wrote none.
    ///
    /// The update's labels are this module's and the field's are whichever
    /// module the type's chain reached, so the two are compared by name.
    fn writtenField(
        self: *Reifier,
        written: []const checked.CheckedRecordExprField,
        field: FieldRef,
    ) ?CheckedExprId {
        for (written) |update| {
            if (self.sameFieldLabel(update.label, field.reader, field.field.name)) return update.value;
        }
        return null;
    }

    /// Every field a record update has to write, by the type of the record it
    /// builds.
    ///
    /// An optional field the update did not write is what stops this: the
    /// result carries whatever the subject had, and a `Field` read of a field
    /// that may be absent is not that. So a type with one is refused rather
    /// than described as a record that always has it.
    fn updatedRecordFields(
        self: *Reifier,
        collected: *std.ArrayList(FieldRef),
        type_id: CheckedTypeId,
        region: base.Region,
    ) Error!void {
        switch (self.types.payload(type_id)) {
            .record => |record| try self.collectRecordFields(collected, record.fields, record.ext, region),
            .empty_record => {},
            .alias => |alias| return self.updatedRecordFields(collected, alias.backing, region),
            .flex, .rigid, .pending, .err => return self.rejectError(.unresolved_type, region, "a record update whose type is unresolved"),
            .tuple,
            .function,
            .nominal,
            .tag_union,
            .empty_tag_union,
            => return self.rejectError(.unsupported_expression, region, "a record update over a type that is not a record"),
        }
        for (collected.items) |field| {
            if (field.field.kind.tag == .optional) {
                return self.rejectError(.unsupported_expression, region, "a record update over a record with an optional field");
            }
        }
    }

    /// Whether an expression describes as a node that reads a name, so a
    /// description may read it more than once without binding it.
    fn readsAName(self: *Reifier, expr_id: CheckedExprId) bool {
        const data = self.bodies.expr(expr_id).data;
        if (data != .lookup_local) return false;
        const binder = self.bodies.patternBinderForCheckedPattern(data.lookup_local.pattern) orelse return false;
        const binding = self.lookupBinding(binder) orelse return false;
        return switch (binding.kind) {
            .param, .local => true,
            .constant, .function, .callee => false,
        };
    }

    /// A field access path, one node per segment it walks.
    ///
    /// A segment written `.?` reads a field the type marks optional and hands
    /// back the `Try(a, [MissingField])` the value sits in, so it describes as
    /// an `OptField` rather than a `Field`. The checker gives the whole path
    /// one flat `Try` however many `.?` segments it holds, which nested nodes
    /// cannot say, so an optional segment is described only where it is the
    /// path's last and the `Try` is therefore the path's own type.
    fn fieldAccessNode(
        self: *Reifier,
        receiver_id: CheckedExprId,
        segments: []const checked.CheckedFieldAccessSegment,
        path_meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var node = try self.irNode(receiver_id);
        for (segments, 1..) |segment, walked| {
            const name = try self.strNode(self.names.recordFieldLabelText(segment.field_name));
            if (segment.mode == .optional) {
                if (walked != segments.len) {
                    return self.reject(.unsupported_expression, region, "a field read through an optional field");
                }
                node = try self.tag("OptField", &.{ node, name, path_meta });
                continue;
            }
            const ty = try self.tyNode(segment.success_ty, segment.source_region);
            const meta = try self.metaNode(ty, segment.source_region);
            node = try self.tag("Field", &.{ node, name, meta });
        }
        return node;
    }

    fn literalNode(
        self: *Reifier,
        data: checked.CheckedNumeralData,
        checked_ty: CheckedTypeId,
        ty: ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const primitive = self.primitiveOf(checked_ty) orelse {
            // A literal of the author's own type is the `from_numeral` call
            // the checker wrote, described rather than folded past: the
            // conversion may validate or clamp, and a translator handed only
            // the number would be guessing at what the author wrote down.
            const plan_id = data.plan orelse
                return self.reject(.unresolved_type, region, "this numeric literal");
            return self.dispatchNode(plan_id, meta, region);
        };
        const lit = try self.numeralLit(data.literal, primitive, ty, region);
        return self.tag("Lit", &.{ lit, meta });
    }

    /// A string literal of more than one segment: the concatenation it is.
    ///
    /// The checker leaves the segments flat, text and value alternating, and
    /// every one of them is a `Str` by the time the walk reads them, so the
    /// description is the fold `Str.from_interpolation` writes itself: one
    /// `concat` per join, named the way every other builtin call is named. A
    /// translator emitting `||` or `+` needs nothing beyond that.
    ///
    /// An empty segment joins nothing to anything and the author wrote no
    /// text there, so it is left out: `"${name}"` carries one on each side
    /// and describes as the name alone.
    fn interpolatedNode(
        self: *Reifier,
        segments: []const CheckedExprId,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        var joined: ?ConstNodeId = null;
        for (segments) |segment| {
            if (self.isEmptySegment(segment)) continue;
            const next = try self.irNode(segment);
            joined = if (joined) |acc| try self.concatNode(acc, next, meta) else next;
        }
        if (joined) |node| return node;
        const text = try self.strNode("");
        const lit = try self.tag("Str", &.{text});
        return self.tag("Lit", &.{ lit, meta });
    }

    /// Whether one segment of a string literal is text the author left empty.
    fn isEmptySegment(self: *Reifier, expr_id: CheckedExprId) bool {
        const data = self.bodies.expr(expr_id).data;
        if (data != .str_segment) return false;
        return self.bodies.stringLiteral(data.str_segment).len == 0;
    }

    /// One join of an interpolated literal, as the builtin call it is.
    fn concatNode(
        self: *Reifier,
        lhs: ConstNodeId,
        rhs: ConstNodeId,
        meta: ConstNodeId,
    ) Error!ConstNodeId {
        const name = try self.strNode(str_concat_name);
        const args = try self.store.append(.{ .list = .{ .nodes = &.{ lhs, rhs } } });
        return self.tag("Call", &.{ name, args, meta });
    }

    /// The literal the compiler handed to a `from_numeral` conversion.
    ///
    /// The declared parameter is `Num.Numeral`, an opaque the compiler threads
    /// to plumb the conversion and that a translator has no reason to model,
    /// so the description carries the number the author wrote instead. A
    /// numeral names no width, so it takes the widest form `Code.Lit` holds:
    /// `I128` for a whole number, `F64` for a fractional one.
    fn generatedNumeralNode(
        self: *Reifier,
        literal: ModuleEnv.NumeralLiteral,
        region: base.Region,
    ) Error!ConstNodeId {
        const exact = self.env.exactNumeral(literal);
        const primitive: checked.CheckedBuiltinNominal = if (exact.is_fractional) .f64 else .i128;
        const ty = try self.tag(primitiveTagName(primitive).?, &.{});
        const lit = try self.numeralLit(literal, primitive, ty, region);
        const meta = try self.metaNode(ty, region);
        return self.tag("Lit", &.{ lit, meta });
    }

    /// The text the compiler handed to a `from_quote` conversion.
    ///
    /// The conversion receives the post-escape bytes as a `Str`, so that is
    /// what the description carries, and the call beside it says what reads
    /// them.
    fn generatedQuoteNode(
        self: *Reifier,
        literal: checked.CheckedStringLiteralId,
        region: base.Region,
    ) Error!ConstNodeId {
        const text = try self.strNode(self.bodies.stringLiteral(literal));
        const lit = try self.tag("Str", &.{text});
        const ty = try self.tag("Str", &.{});
        const meta = try self.metaNode(ty, region);
        return self.tag("Lit", &.{ lit, meta });
    }

    /// The `Lit` a numeric literal describes as. A pattern carries the same
    /// `Lit` without the `Ir` node around it, which is why this is its own
    /// step.
    fn numeralLit(
        self: *Reifier,
        literal: ModuleEnv.NumeralLiteral,
        primitive: checked.CheckedBuiltinNominal,
        ty: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        const exact = self.env.exactNumeral(literal);
        const lit = switch (primitive) {
            // `Lit.Frac` carries an F64, so an F32 literal rounds to F32 first:
            // the stage sees the value the program will actually hold.
            .f32 => blk: {
                const value = try numeral.floatBits(f32, self.gpa, exact);
                const bits = try self.store.append(.{ .scalar = .{ .f64_bits = @bitCast(@as(f64, value)) } });
                break :blk try self.tag("Frac", &.{ bits, ty });
            },
            .f64 => blk: {
                const value = try numeral.floatBits(f64, self.gpa, exact);
                const bits = try self.store.append(.{ .scalar = .{ .f64_bits = @bitCast(value) } });
                break :blk try self.tag("Frac", &.{ bits, ty });
            },
            .dec => blk: {
                const value = try numeral.decBits(self.gpa, exact) orelse
                    return self.reject(.unsupported_expression, region, "this numeric literal");
                const bits = try self.store.append(.{ .scalar = .{ .dec_bits = value } });
                break :blk try self.tag("Fixed", &.{bits});
            },
            .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => blk: {
                const target = intTarget(primitive);
                const value = switch (numeral.intBits(exact, target) orelse
                    return self.reject(.unsupported_expression, region, "this numeric literal")) {
                    .i128 => |signed| signed,
                    // Only the u128 target reaches here, and `Lit.Int` is an
                    // I128, so the bit pattern is what carries the value.
                    .u128 => |magnitude| @as(i128, @bitCast(magnitude)),
                };
                const bits = try self.store.append(.{ .scalar = .{ .i128 = value } });
                break :blk try self.tag("Int", &.{ bits, ty });
            },
            .bool,
            .try_,
            .str,
            .u8x16,
            .i8x16,
            .u16x8,
            .i16x8,
            .u32x4,
            .i32x4,
            .u64x2,
            .i64x2,
            .list,
            .box,
            .dict,
            .set,
            .iter,
            .stream,
            .parse_tag_union_spec,
            .fields,
            .field,
            .crypto_sha256_digest,
            .crypto_sha256_hasher,
            .crypto_blake3_digest,
            .crypto_blake3_hasher,
            => return self.reject(.unsupported_type, region, "a numeric literal of this type"),
        };
        return lit;
    }

    // Ty //

    fn tyNode(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!ConstNodeId {
        // Resolving at the leaf is enough: a composite holding a variable is
        // reached by recursion into the variable itself.
        if (self.fixedType(type_id)) |fixed| {
            self.substitution_uses += 1;
            return fixed.reader.tyNode(fixed.id, region);
        }
        if (self.type_cache.get(type_id)) |cached| return cached;
        const frame = TypeFrame{ .instance = self.nominal_instance, .id = type_id };
        if (self.type_in_progress.contains(frame)) {
            return self.reject(.unsupported_type, region, "a recursive type");
        }

        try self.type_in_progress.put(self.gpa, frame, {});
        defer _ = self.type_in_progress.remove(frame);

        const open_before = self.open_recursions.count();
        const uses_before = self.substitution_uses;
        const node = try self.buildTyNode(type_id, region);

        // Cache only a subtree that stands alone, because `type_cache` is keyed
        // by type id and a subtree still holding an open `Recursive` would mean
        // something else outside the `Named` it was built under. A subtree a
        // substitution answered inside means something else at the next
        // instantiation, which is the same reason.
        if (self.open_recursions.count() == open_before and self.substitution_uses == uses_before) {
            try self.type_cache.put(self.gpa, type_id, node);
        }
        return node;
    }

    fn buildTyNode(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!ConstNodeId {
        const payload = self.types.payload(type_id);
        return switch (payload) {
            .alias => |alias| self.tyNode(alias.backing, region),
            // A row variable nothing pins is the row default lowering seals it
            // to (design.md "Row Coercion Primitive": a value keeps its own
            // row, so a tag built before its widening holds the variable in
            // its own type).
            .flex => |variable| if (payload.variableSealsToRowDefault()) switch (variable.row_default.?) {
                .empty_record => self.emptyRecordTyNode(),
                .empty_tag_union => self.emptyTagUnionTyNode(),
            } else self.reject(.unresolved_type, region, "a type variable"),
            .rigid => self.reject(.unresolved_type, region, "a type variable"),
            .pending, .err => self.reject(.unresolved_type, region, "an unresolved type"),
            .empty_record => self.emptyRecordTyNode(),
            .record => |record| self.recordTyNode(record.fields, record.ext, region),
            .tuple => |elements| blk: {
                const nodes = try self.tyNodes(elements, region);
                defer self.gpa.free(nodes);
                const list = try self.store.append(.{ .list = .{ .nodes = nodes } });
                break :blk try self.tag("Tuple", &.{list});
            },
            .function => |function| blk: {
                if (function.kind == .effectful) {
                    break :blk try self.reject(.effect, region, "an effectful function");
                }
                const args = try self.tyNodes(function.args, region);
                defer self.gpa.free(args);
                const list = try self.store.append(.{ .list = .{ .nodes = args } });
                const ret = try self.tyNode(function.ret, region);
                break :blk try self.tag("Fn", &.{ list, ret });
            },
            .nominal => |nominal| self.nominalTyNode(type_id, nominal, region),
            .tag_union => |tag_union| self.tagUnionTyNode(tag_union.tags, tag_union.ext, region),
            .empty_tag_union => self.emptyTagUnionTyNode(),
        };
    }

    fn emptyRecordTyNode(self: *Reifier) Allocator.Error!ConstNodeId {
        const fields = try self.store.append(.{ .list = .{ .nodes = &.{} } });
        return self.tag("Record", &.{fields});
    }

    fn emptyTagUnionTyNode(self: *Reifier) Allocator.Error!ConstNodeId {
        const variants = try self.store.append(.{ .list = .{ .nodes = &.{} } });
        return self.tag("TagUnion", &.{variants});
    }

    /// A tag union's variants, described in the order the walk collects them.
    fn tagUnionTyNode(
        self: *Reifier,
        tags: []const checked.CheckedTag,
        ext: CheckedTypeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var collected = std.ArrayList(checked.CheckedTag).empty;
        defer collected.deinit(self.gpa);
        try self.collectVariants(&collected, tags, ext, region);

        var variants = std.ArrayList(ConstNodeId).empty;
        defer variants.deinit(self.gpa);
        for (collected.items) |checked_tag| {
            try variants.append(self.gpa, try self.variantEntry(checked_tag, region));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = variants.items } });
        return self.tag("TagUnion", &.{list});
    }

    /// Every variant of a tag union, following its extension.
    ///
    /// A checked tag union holds the variants solved at one point and an
    /// extension type carrying the rest, the way a record does, so the walk
    /// follows the chain to its end.
    ///
    /// An extension the checker closed ends it. Closing a row leaves a variable
    /// behind rather than an `empty_tag_union`, marked with the default that
    /// says what it closed to, so `checkedRowVariableClosesTagRow` is the one
    /// reading of a variable found here. A variable without that mark names a
    /// row still open, and a description is monomorphic.
    fn collectVariants(
        self: *Reifier,
        collected: *std.ArrayList(checked.CheckedTag),
        tags: []const checked.CheckedTag,
        ext: CheckedTypeId,
        region: base.Region,
    ) Error!void {
        var link_tags = tags;
        var link_ext: ?CheckedTypeId = ext;
        while (true) {
            try collected.appendSlice(self.gpa, link_tags);
            const next = link_ext orelse break;
            switch (self.types.payload(next)) {
                .empty_tag_union => break,
                .tag_union => |more| {
                    link_tags = more.tags;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_tags = &.{};
                    link_ext = alias.backing;
                },
                .flex, .rigid => |variable| {
                    if (!checked.checkedRowVariableClosesTagRow(variable)) {
                        return self.rejectError(.unresolved_type, region, "an open tag union");
                    }
                    break;
                },
                .pending, .err => return self.rejectError(.unresolved_type, region, "an unresolved type"),
                .record,
                .empty_record,
                .tuple,
                .function,
                .nominal,
                => return self.rejectError(.unsupported_type, region, "a tag union extended by a type that is not a tag union"),
            }
        }
    }

    /// One `{ name, payloads }` variant of a `Ty.TagUnion`.
    fn variantEntry(self: *Reifier, checked_tag: checked.CheckedTag, region: base.Region) Error!ConstNodeId {
        const args = checked_tag.argsSlice(self.types);
        const payload_nodes = try self.tyNodes(args, region);
        defer self.gpa.free(payload_nodes);
        const payloads = try self.store.append(.{ .list = .{ .nodes = payload_nodes } });
        const name = try self.strNode(self.names.tagLabelText(checked_tag.name));
        return self.store.append(.{ .record = &.{ name, payloads } });
    }

    fn nominalTyNode(
        self: *Reifier,
        type_id: CheckedTypeId,
        nominal: checked.CheckedNominalType,
        region: base.Region,
    ) Error!ConstNodeId {
        if (nominal.builtin) |builtin_nominal| {
            if (primitiveTagName(builtin_nominal)) |name| return self.tag(name, &.{});
            if (builtin_nominal == .list) {
                if (nominal.args.len != 1) {
                    return self.reject(.unsupported_type, region, "List");
                }
                const element = try self.tyNode(nominal.args[0], region);
                return self.tag("ListOf", &.{element});
            }
            return self.opaqueTyNode(nominal, region);
        }

        // An opaque nominal forbids reading its backing from outside its own
        // module, and a stage is always outside it.
        if (nominal.is_opaque) return self.opaqueTyNode(nominal, region);

        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.opaqueTyNode(nominal, region);
        const name = try self.strNode(self.names.typeNameText(nominal.name));

        // The backing is the declaration's template, written in the nominal's
        // own variables, and `args` is what this use fixed them to. Binding
        // the two for the span of the walk is what makes `Box(F32)` read as a
        // `Box` of `F32` rather than as a type variable, the way a call fixes
        // a generic callee's variables for the span of its body.
        var bound_args = try self.bindNominalArgs(nominal);
        defer self.releaseNominalArgs(&bound_args);

        // The backing is where a nominal reaches itself, and the `Named` this
        // builds is what such a reference names, so open the reference before
        // descending and close it after.
        //
        // What is open is this nominal at these arguments, not the id the use
        // carries: the backing is the declaration's template, so a use with
        // type arguments reaches itself under the id the declaration wrote.
        const instance = self.nominalInstanceKey(nominal);
        if (self.nominal_in_progress.get(instance)) |open| {
            try self.open_recursions.put(self.gpa, open, {});
            // What this answers depends on what the enclosing use fixed, the
            // same way a substitution's answer does, so the frame that asked
            // declines to cache it.
            self.substitution_uses += 1;
            return self.tag("Recursive", &.{name});
        }
        try self.nominal_in_progress.put(self.gpa, instance, type_id);
        defer _ = self.nominal_in_progress.remove(instance);

        const enclosing = self.nominal_instance;
        self.nominal_instance = instance;
        defer self.nominal_instance = enclosing;

        const backing_ty = try self.tyNode(backing, region);
        _ = self.open_recursions.remove(type_id);

        return self.tag("Named", &.{ name, backing_ty });
    }

    /// A key for one nominal at one instantiation: the declaration, and what
    /// this use fixed its variables to.
    ///
    /// Digested from each argument's canonical key rather than from its id, the
    /// way `instantiationKey` digests a call's, because an id is canonical only
    /// inside one module.
    fn nominalInstanceKey(self: *Reifier, nominal: checked.CheckedNominalType) [32]u8 {
        var hasher = std.crypto.hash.Blake3.init(.{});
        hasher.update(std.mem.asBytes(&@backingInt(nominal.origin_module)));
        hasher.update(std.mem.asBytes(&@backingInt(nominal.name)));
        hasher.update(std.mem.asBytes(&nominal.source_decl));
        for (nominal.args) |arg| {
            const bound = self.resolvedType(arg);
            hasher.update(&bound.reader.types.rootKey(bound.id).bytes);
        }
        var key: [32]u8 = undefined;
        hasher.final(&key);
        return key;
    }

    /// What one parametric nominal bound, and what stood in its place before.
    ///
    /// A nominal inside another's backing binds the same declared variables to
    /// other types, so the walk restores rather than removes: the outer
    /// binding is still what the rest of the outer backing reads.
    const NominalArgs = struct {
        formals: []const CheckedTypeId = &.{},
        outer: []?TypeRef = &.{},
    };

    /// Bind a parametric nominal's declared variables to what this use fixed
    /// them to.
    ///
    /// Binds nothing when the nominal declares no variables, or when the
    /// declaration and the use disagree on how many there are, which leaves
    /// the backing reading as the variables it still holds.
    fn bindNominalArgs(
        self: *Reifier,
        nominal: checked.CheckedNominalType,
    ) Allocator.Error!NominalArgs {
        if (nominal.args.len == 0) return .{};
        const declaration = self.types.nominalDeclarationForPayload(nominal) orelse return .{};
        const formals = declaration.formalArgs(self.types);
        if (formals.len != nominal.args.len) return .{};

        // Every use is read before any formal is bound, so one formal's
        // binding cannot answer another's.
        const fixed = try self.gpa.alloc(TypeRef, nominal.args.len);
        defer self.gpa.free(fixed);
        for (nominal.args, 0..) |arg, index| fixed[index] = self.resolvedType(arg);

        const outer = try self.gpa.alloc(?TypeRef, formals.len);
        errdefer self.gpa.free(outer);
        for (formals, fixed, 0..) |formal, use, index| {
            outer[index] = self.nominal_args.get(formal);
            try self.nominal_args.put(self.gpa, formal, use);
        }
        return .{ .formals = formals, .outer = outer };
    }

    /// Put back what stood for these variables before the nominal bound them.
    fn releaseNominalArgs(self: *Reifier, bound: *NominalArgs) void {
        for (bound.formals, bound.outer) |formal, outer| {
            if (outer) |restored| {
                self.nominal_args.getPtr(formal).?.* = restored;
            } else {
                _ = self.nominal_args.remove(formal);
            }
        }
        self.gpa.free(bound.outer);
    }

    /// A nominal the IR has no shape for, named with its type arguments. A
    /// derived implementation threads values of these types without looking
    /// inside them, so naming one is all a stage needs to recognise or refuse
    /// it.
    fn opaqueTyNode(
        self: *Reifier,
        nominal: checked.CheckedNominalType,
        region: base.Region,
    ) Error!ConstNodeId {
        const name = try self.strNode(self.names.typeNameText(nominal.name));
        const args = try self.tyNodes(nominal.args, region);
        defer self.gpa.free(args);
        const list = try self.store.append(.{ .list = .{ .nodes = args } });
        return self.tag("Opaque", &.{ name, list });
    }

    /// A record type's fields, following its extension.
    ///
    /// A checked record holds the fields solved at one point and an extension
    /// type carrying the rest, so `{ uv : Vec2, time : F32 }` can arrive as one
    /// field extended by the other. A stage reads the whole record, so the walk
    /// follows the chain to its end.
    fn recordTyNode(
        self: *Reifier,
        fields: []const checked.CheckedRecordField,
        ext: ?CheckedTypeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var collected = std.ArrayList(FieldRef).empty;
        defer collected.deinit(self.gpa);
        try self.collectRecordFields(&collected, fields, ext, region);

        var entries = std.ArrayList(ConstNodeId).empty;
        defer entries.deinit(self.gpa);
        for (collected.items) |field| {
            const ty = try field.reader.tyNode(field.field.ty, region);
            const label = field.reader.names.recordFieldLabelText(field.field.name);
            try entries.append(self.gpa, try self.recordTypeEntry(label, ty, field.field.kind, region));
        }

        const list = try self.store.append(.{ .list = .{ .nodes = entries.items } });
        return self.tag("Record", &.{list});
    }

    /// Every field of a record type, following its extension.
    ///
    /// A record's fields arrive split across the links of an extension chain.
    /// The type walk needs all of them to describe the shape, and a record
    /// update needs all of them to know which fields it did not name, so both
    /// read the chain here.
    ///
    /// A chain ending in a variable the site fixed carries on in the site's
    /// module: the definition wrote the fields it named and the site's record
    /// holds the rest. That record holds the named fields too, so a field
    /// already collected is dropped where it comes round a second time.
    fn collectRecordFields(
        self: *Reifier,
        collected: *std.ArrayList(FieldRef),
        fields: []const checked.CheckedRecordField,
        ext: ?CheckedTypeId,
        region: base.Region,
    ) Error!void {
        var reader = self;
        var link_fields = fields;
        var link_ext = ext;
        while (true) {
            for (link_fields) |field| try self.collectField(collected, reader, field);
            const next = link_ext orelse break;
            switch (reader.types.payload(next)) {
                .empty_record => break,
                .record => |record| {
                    link_fields = record.fields;
                    link_ext = record.ext;
                },
                .alias => |alias| {
                    link_fields = &.{};
                    link_ext = alias.backing;
                },
                // An extension is a type variable, and what the site fixed it
                // to is the rest of the record. Where the site fixed nothing
                // the record has no fixed set of fields, so there is no shape
                // to describe.
                .flex, .rigid => {
                    const bound = reader.fixedType(next) orelse
                        return self.rejectError(.unresolved_type, region, "an open record");

                    // The fields from here on are what one site fixed, so the
                    // frame that asked declines to cache this node.
                    self.substitution_uses += 1;
                    reader = bound.reader;
                    link_fields = &.{};
                    link_ext = bound.id;
                },
                .pending, .err => return self.rejectError(.unresolved_type, region, "an unresolved type"),
                .tuple,
                .function,
                .nominal,
                .tag_union,
                .empty_tag_union,
                => return self.rejectError(.unsupported_type, region, "a record extended by a type that is not a record"),
            }
        }
    }

    /// Collect one field, unless a link nearer the front of the chain already
    /// named it. The nearer link is the one the type means, and a site's record
    /// repeats every field the definition named.
    fn collectField(
        self: *Reifier,
        collected: *std.ArrayList(FieldRef),
        reader: *Reifier,
        field: checked.CheckedRecordField,
    ) Allocator.Error!void {
        for (collected.items) |seen| {
            if (seen.reader.sameFieldLabel(seen.field.name, reader, field.name)) return;
        }
        try collected.append(self.gpa, .{ .reader = reader, .field = field });
    }

    /// One entry of a record type: the field, and whether the type says a
    /// value of it carries the field.
    ///
    /// A field with a default is `Required`, because the default fills it in
    /// and every value of the type has it. So is one whose presence the
    /// checker never pinned: an unpinned presence is what the checker itself
    /// commits to required (`src/check/Check.zig:19122`), and the two uses
    /// that pin one to optional, an unset field and a `.?` read, are both in
    /// front of the walk where it meets them. Only an optional field may be
    /// absent, and a translator either has a form for absence or rejects the
    /// type by name.
    fn recordTypeEntry(
        self: *Reifier,
        name: []const u8,
        ty: ConstNodeId,
        kind: checked.CheckedFieldKind,
        region: base.Region,
    ) Error!ConstNodeId {
        const presence = switch (kind.tag) {
            .required, .defaulted, .undetermined => try self.tag("Required", &.{}),
            .optional => try self.tag("Optional", &.{}),
            .err => return self.reject(.unresolved_type, region, "a record field whose presence is an error"),
        };
        const name_node = try self.strNode(name);
        return self.store.append(.{ .record = &.{ name_node, presence, ty } });
    }

    fn tyNodes(self: *Reifier, ids: []const CheckedTypeId, region: base.Region) Error![]ConstNodeId {
        const nodes = try self.gpa.alloc(ConstNodeId, ids.len);
        errdefer self.gpa.free(nodes);
        for (ids, 0..) |id, index| nodes[index] = try self.tyNode(id, region);
        return nodes;
    }

    // scope //

    fn bindParam(self: *Reifier, pattern_id: CheckedPatternId, region: base.Region) Error![]const u8 {
        return self.bind(pattern_id, .param, region);
    }

    /// A parameter written as a pattern takes its argument apart the way a
    /// destructuring binding does: the parameter goes by a name of its own,
    /// and the reads the pattern stands for are appended for the body to sit
    /// under. `|(a, b)| ..` describes as `|bind#0| let a = bind#0.0; ..`.
    fn bindParamPattern(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        destructures: *std.ArrayList(Destructure),
        region: base.Region,
    ) Error![]const u8 {
        if (self.bodies.pattern(pattern_id).data == .assign) return self.bindParam(pattern_id, region);
        const name = try self.inventedName();
        const read = try self.tag("Param", &.{ try self.strNode(name), try self.patternMeta(pattern_id) });
        try self.destructureInto(destructures, pattern_id, read, true, region);
        return name;
    }

    fn bindLocal(self: *Reifier, pattern_id: CheckedPatternId, region: base.Region) Error![]const u8 {
        return self.bind(pattern_id, .local, region);
    }

    fn bind(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        kind: Binding.Kind,
        region: base.Region,
    ) Error![]const u8 {
        const pattern = self.bodies.pattern(pattern_id);
        const binder = switch (pattern.data) {
            .assign => |binder| binder,
            .pending,
            .as,
            .applied_tag,
            .nominal,
            .record_destructure,
            .list,
            .tuple,
            .numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => return self.rejectError(.unsupported_expression, region, "a destructuring pattern"),
        };
        return self.bindBinder(binder, kind);
    }

    /// Puts one binder in the staged scope under the name it goes by.
    fn bindBinder(
        self: *Reifier,
        binder: checked.PatternBinderId,
        kind: Binding.Kind,
    ) Error![]const u8 {
        const name = try self.bindingName(binder);
        try self.scope.append(self.gpa, .{ .binder = binder, .name = name, .kind = kind });
        return name;
    }

    /// The name one binder goes by in the description. A binder a replayed
    /// statement binds keeps the name its reads already carry.
    fn bindingName(self: *Reifier, binder: checked.PatternBinderId) Allocator.Error![]const u8 {
        if (self.replay) |replay| {
            if (replay.bindings.get(binder)) |recorded| return recorded.name;
        }
        const written = self.binderName(binder);
        return if (isWrittenName(written)) written else try self.inventedName();
    }

    /// A name for a binder no author wrote.
    ///
    /// The `?` operators and the comparison a derived `==` expands to bind
    /// names the compiler spells with characters no target accepts. The `Ir`
    /// names its bindings, so the walk gives one a name of its own: unique
    /// across the description, and nothing more is asked of it, because there
    /// is no written name to preserve. The serial goes on the spelling the way
    /// C17d puts one on a lifted row's.
    fn inventedName(self: *Reifier) Allocator.Error![]const u8 {
        const serial = try self.walk.nameSerial("bind");
        const name = try std.fmt.allocPrint(self.gpa, "bind#{d}", .{serial});
        errdefer self.gpa.free(name);
        try self.invented_names.append(self.gpa, name);
        return name;
    }

    /// What a lambda captured from around itself, empty when it captured
    /// nothing. A plain lambda is the closure's body and holds none.
    fn capturesOf(self: *Reifier, expr_id: CheckedExprId) []const checked.CheckedCapture {
        const data = self.bodies.expr(expr_id).data;
        if (data != .closure) return &.{};
        return data.closure.captures;
    }

    /// Whether a capture names something the staged scope already binds.
    fn capturedInScope(self: *Reifier, pattern_id: CheckedPatternId) bool {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse return false;
        return self.lookupBinding(binder) != null;
    }

    /// What a capture is called, for the refusal that names it.
    fn capturedName(self: *Reifier, pattern_id: CheckedPatternId) []const u8 {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse
            return "a value from the surrounding scope";
        return self.binderName(binder);
    }

    fn lookupBinding(self: *Reifier, binder: checked.PatternBinderId) ?Binding {
        var index = self.scope.items.len;
        while (index > 0) {
            index -= 1;
            if (self.scope.items[index].binder == binder) return self.scope.items[index];
        }
        const replay = self.replay orelse return null;
        return replay.bindings.get(binder);
    }

    /// The statement that binds a name the root reads from the block around
    /// it, or null where nothing replays it: no root is being walked, a
    /// parameter, a branch, a loop or a `var` binds the name, or the
    /// statement sits inside the root and the walk binds it there.
    fn replayStatement(self: *Reifier, pattern_id: CheckedPatternId) ?CheckedStatementId {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse return null;
        return self.replayStatementOf(binder);
    }

    fn replayStatementOf(self: *Reifier, binder: checked.PatternBinderId) ?CheckedStatementId {
        const replay = self.replay orelse return null;
        const statement_id = self.bodies.patternBinder(binder).defining_statement orelse return null;
        const statement = self.bodies.statement(statement_id).source_region;
        if (statement.start.offset >= replay.region.start.offset and statement.end.offset <= replay.region.end.offset) return null;
        return statement_id;
    }

    /// Resolve a name the root reads from the block around it, recording the
    /// statement that binds it for `replayedNode` to wrap the body in.
    ///
    /// A binding that holds a function is held, the way the block walk holds
    /// one, so it replays as nothing: the call that runs it lifts it into a
    /// row. Every other binding is read as a local until its statement binds
    /// it at the head of the body.
    fn replayBinding(self: *Reifier, binder: checked.PatternBinderId) Error!?Binding {
        const statement_id = self.replayStatementOf(binder) orelse return null;
        const replay = self.replay.?;
        const decl = self.bodies.statement(statement_id).data.decl;
        const holds_function = self.functionOf(self.bodies.expr(decl.expr).ty) != null;
        const binding: Binding = if (holds_function)
            .{ .binder = binder, .name = self.binderName(binder), .kind = .{ .function = decl.expr } }
        else
            .{ .binder = binder, .name = try self.bindingName(binder), .kind = .local };
        try replay.bindings.put(self.gpa, binder, binding);
        if (!holds_function) {
            for (replay.pending.items) |pending| {
                if (pending == statement_id) return binding;
            }
            try replay.pending.append(self.gpa, statement_id);
        }
        return binding;
    }

    /// Wrap a root's body in the statements it reads from around it.
    ///
    /// A statement reads only what the statements before it bind, so each
    /// wrap takes the latest pending statement in the source. Replaying one
    /// can record more, and those sit earlier than every statement wrapped so
    /// far, so the body ends up under the statements in the order they were
    /// written.
    fn replayedNode(
        self: *Reifier,
        replay: *Replay,
        body: ConstNodeId,
        meta: ConstNodeId,
        region: base.Region,
    ) Error!ConstNodeId {
        var node = body;
        while (replay.pending.items.len != 0) {
            var latest: usize = 0;
            for (replay.pending.items, 0..) |pending, index| {
                const at = self.bodies.statement(pending).source_region.start.offset;
                if (at > self.bodies.statement(replay.pending.items[latest]).source_region.start.offset) latest = index;
            }
            const statement = replay.pending.swapRemove(latest);
            const one = [_]CheckedStatementId{statement};
            node = try self.statementsNode(
                .{ .statements = &one, .ending = .{ .node = node }, .escapes = false },
                meta,
                region,
            );
        }
        return node;
    }

    /// An `assign` pattern's region is exactly its identifier, and an `as`
    /// pattern's region ends at the identifier it binds, so both name a binder
    /// through the source. Regions survive serialization where the source-node
    /// map does not, which is why the name comes from here rather than from a
    /// pattern's canonical node.
    ///
    /// One `assign` reads wider than its identifier: a string pattern's
    /// capture carries the interpolation that wrote it, braces and all.
    fn binderName(self: *Reifier, binder: checked.PatternBinderId) []const u8 {
        const record = self.bodies.patternBinder(binder);
        const pattern = self.bodies.pattern(record.pattern);
        const text = self.env.getSource(pattern.source_region);
        return switch (pattern.data) {
            .as => trailingIdentifier(text),
            .assign => interpolatedIdentifier(text),
            .pending,
            .applied_tag,
            .nominal,
            .record_destructure,
            .list,
            .tuple,
            .numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => text,
        };
    }

    // helpers //

    fn tag(self: *Reifier, name: []const u8, payloads: []const ConstNodeId) Allocator.Error!ConstNodeId {
        return self.store.append(.{ .tag = .{ .tag_name = name, .payloads = payloads } });
    }

    /// The `Meta` every `Ir` node carries: the type the checker solved, and
    /// where the node was written.
    ///
    /// The region is resolved to lines and columns here rather than left as
    /// byte offsets, because a stage holds a description and never the source
    /// text an offset would need. The lines are the ones the author's file
    /// shows, so a stage's message and the compiler's own reports agree.
    fn metaNode(self: *Reifier, ty: ConstNodeId, region: base.Region) Allocator.Error!ConstNodeId {
        const module = try self.strNode(if (self.folded_origin) |origin|
            origin.module
        else
            self.env.module_name);
        const info = if (self.folded_origin) |origin|
            origin.info
        else
            self.env.calcAuthoredRegionInfo(region);
        // A constant record's fields are restored in label order, not in the
        // order the type declares them, so both records are built sorted.
        const region_node = try self.store.append(.{ .record = &.{
            try self.u32Node(info.end_col_idx + 1),
            try self.u32Node(info.end_line_idx + 1),
            module,
            try self.u32Node(info.start_col_idx + 1),
            try self.u32Node(info.start_line_idx + 1),
        } });
        return self.store.append(.{ .record = &.{ region_node, ty } });
    }

    fn u32Node(self: *Reifier, value: u32) Allocator.Error!ConstNodeId {
        return self.store.append(.{ .scalar = .{ .u32 = value } });
    }

    /// A `Str` node, shared with every other node of the same text.
    ///
    /// A description names the same few strings over and over: one module name
    /// per `Region`, one operator name per arithmetic node, one field name per
    /// read of that field. A node id is a shared reference already, so the
    /// second `"plus"` is the first.
    ///
    /// Keyed by the blob the text interned to rather than by the text itself.
    /// `addBlobData` has already hashed the bytes and owns a copy of them, so
    /// a text key would hash them a second time and need a second copy to
    /// outlive whatever the caller borrowed the text from.
    fn strNode(self: *Reifier, text: []const u8) Allocator.Error!ConstNodeId {
        const data = try self.store.addBlobData(text);
        const shared = try self.walk.str_nodes.getOrPut(self.gpa, data);
        if (shared.found_existing) return shared.value_ptr.*;
        shared.value_ptr.* = try self.store.append(.{ .str = .{
            .data = data,
            .offset = 0,
            .len = @intCast(text.len),
        } });
        return shared.value_ptr.*;
    }

    /// A `List(U8)` held as one blob rather than one node per byte, because an
    /// embedded file is as large as the file is.
    fn bytesNode(self: *Reifier, bytes: []const u8) Allocator.Error!ConstNodeId {
        const data = try self.store.addBlobData(bytes);
        return self.store.append(.{ .list = .{ .packed_bytes = .{
            .bytes = .{ .data = data, .offset = 0, .len = @intCast(bytes.len) },
            .len = @intCast(bytes.len),
            .element = .u8,
        } } });
    }

    /// One `{ name, ty }` record, the element shape shared by `Lambda`'s
    /// parameter list and `Ty.Record`'s field list.
    fn namedTypeEntry(self: *Reifier, name: []const u8, ty: ConstNodeId) Allocator.Error!ConstNodeId {
        const name_node = try self.strNode(name);
        return self.store.append(.{ .record = &.{ name_node, ty } });
    }

    /// Records the first rejection and unwinds. The `ConstNodeId` result lets
    /// a rejection sit in the value position of a walk arm.
    fn reject(
        self: *Reifier,
        kind: Rejection.Kind,
        region: base.Region,
        detail: []const u8,
    ) Error!ConstNodeId {
        return self.rejectError(kind, region, detail);
    }

    fn rejectError(
        self: *Reifier,
        kind: Rejection.Kind,
        region: base.Region,
        detail: []const u8,
    ) error{Rejected} {
        if (self.walk.rejection == null) {
            self.walk.rejection = .{ .kind = kind, .region = region, .detail = detail };
        }
        return error.Rejected;
    }

    fn functionOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedFunctionType {
        return switch (self.types.payload(type_id)) {
            .function => |function| function,
            .alias => |alias| self.functionOf(alias.backing),
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .tuple,
            .nominal,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => null,
        };
    }

    /// The nominal a checked id is, reading through an alias. Reads this
    /// reader's store alone, because the args it carries are ids of that
    /// store.
    fn nominalOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedNominalType {
        return switch (self.types.payload(type_id)) {
            .nominal => |nominal| nominal,
            .alias => |alias| self.nominalOf(alias.backing),
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .tuple,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => null,
        };
    }

    /// The elements a checked id is a tuple of, reading through an alias.
    fn tupleOf(self: *Reifier, type_id: CheckedTypeId) ?[]const CheckedTypeId {
        return switch (self.types.payload(type_id)) {
            .tuple => |elements| elements,
            .alias => |alias| self.tupleOf(alias.backing),
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .nominal,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => null,
        };
    }

    fn primitiveOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedBuiltinNominal {
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.primitiveOf(resolved.id);
        return switch (self.types.payload(resolved.id)) {
            .alias => |alias| self.primitiveOf(alias.backing),
            .nominal => |nominal| nominal.builtin,
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .tuple,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => null,
        };
    }
};

/// The `Hasher.write_*` method the compiler's own derivation feeds a leaf of
/// this type to, or `null` where it writes no leaf at all. This mirrors
/// `hasherWriteOp` in `src/postcheck/common.zig`, which is what decides the
/// width a staged hash has to agree on.
fn hasherWriteName(primitive: checked.CheckedBuiltinNominal) ?[]const u8 {
    return switch (primitive) {
        .bool => "write_bool",
        .str => "write_str",
        .u8 => "write_u8",
        .i8 => "write_i8",
        .u16 => "write_u16",
        .i16 => "write_i16",
        .u32 => "write_u32",
        .i32 => "write_i32",
        .u64 => "write_u64",
        .i64 => "write_i64",
        .u128 => "write_u128",
        .i128 => "write_i128",
        .f32 => "write_f32",
        .f64 => "write_f64",
        .dec => "write_dec",
        .u8x16, .i8x16, .u16x8, .i16x8, .u32x4, .i32x4, .u64x2, .i64x2 => "write_u128",
        .try_,
        .list,
        .box,
        .dict,
        .set,
        .iter,
        .stream,
        .parse_tag_union_spec,
        .fields,
        .field,
        .crypto_sha256_digest,
        .crypto_sha256_hasher,
        .crypto_blake3_digest,
        .crypto_blake3_hasher,
        => null,
    };
}

/// Whether a derived `==` on this type is one comparison rather than a fold
/// over components.
/// The registry owner key for a builtin nominal, or null when the registry
/// keys it by its declaration.
///
/// `Try` is the one builtin the registry keys as a nominal, because it is a
/// tag union the compiler names rather than a type with its own owner.
fn builtinMethodOwner(builtin: ?checked.CheckedBuiltinNominal) ?static_dispatch.BuiltinOwner {
    const found = builtin orelse return null;
    if (found == .try_) return null;
    return static_dispatch.builtinOwnerForCheckedBuiltin(found);
}

fn isScalarEq(primitive: checked.CheckedBuiltinNominal) bool {
    return switch (primitive) {
        .bool,
        .str,
        .u8,
        .i8,
        .u16,
        .i16,
        .u32,
        .i32,
        .u64,
        .i64,
        .u128,
        .i128,
        .f32,
        .f64,
        .dec,
        => true,
        .try_,
        .u8x16,
        .i8x16,
        .u16x8,
        .i16x8,
        .u32x4,
        .i32x4,
        .u64x2,
        .i64x2,
        .list,
        .box,
        .dict,
        .set,
        .iter,
        .stream,
        .parse_tag_union_spec,
        .fields,
        .field,
        .crypto_sha256_digest,
        .crypto_sha256_hasher,
        .crypto_blake3_digest,
        .crypto_blake3_hasher,
        => false,
    };
}

/// The numeral target for a primitive the `Int` arm has already selected.
fn intTarget(primitive: checked.CheckedBuiltinNominal) numeral.Target {
    return switch (primitive) {
        .u8 => .u8,
        .i8 => .i8,
        .u16 => .u16,
        .i16 => .i16,
        .u32 => .u32,
        .i32 => .i32,
        .u64 => .u64,
        .i64 => .i64,
        .u128 => .u128,
        .i128 => .i128,
        .f32,
        .f64,
        .dec,
        .bool,
        .try_,
        .str,
        .u8x16,
        .i8x16,
        .u16x8,
        .i16x8,
        .u32x4,
        .i32x4,
        .u64x2,
        .i64x2,
        .list,
        .box,
        .dict,
        .set,
        .iter,
        .stream,
        .parse_tag_union_spec,
        .fields,
        .field,
        .crypto_sha256_digest,
        .crypto_sha256_hasher,
        .crypto_blake3_digest,
        .crypto_blake3_hasher,
        => unreachable,
    };
}

fn primitiveTagName(builtin_nominal: checked.CheckedBuiltinNominal) ?[]const u8 {
    return switch (builtin_nominal) {
        .bool => "Bool",
        .str => "Str",
        .u8 => "U8",
        .i8 => "I8",
        .u16 => "U16",
        .i16 => "I16",
        .u32 => "U32",
        .i32 => "I32",
        .u64 => "U64",
        .i64 => "I64",
        .u128 => "U128",
        .i128 => "I128",
        .f32 => "F32",
        .f64 => "F64",
        .dec => "Dec",
        .try_,
        .u8x16,
        .i8x16,
        .u16x8,
        .i16x8,
        .u32x4,
        .i32x4,
        .u64x2,
        .i64x2,
        .list,
        .box,
        .dict,
        .set,
        .iter,
        .stream,
        .parse_tag_union_spec,
        .fields,
        .field,
        .crypto_sha256_digest,
        .crypto_sha256_hasher,
        .crypto_blake3_digest,
        .crypto_blake3_hasher,
        => null,
    };
}

fn binopName(op: @import("can").CIR.Expr.Binop.Op) ?[]const u8 {
    return switch (op) {
        .add => "plus",
        .sub => "minus",
        .mul => "times",
        .div => "div_by",
        .div_trunc => "div_trunc_by",
        .rem => "rem_by",
        .lt => "is_lt",
        .le => "is_lte",
        .gt => "is_gt",
        .ge => "is_gte",
        .eq => "is_eq",
        .ne => "is_not_eq",
        .@"and" => "and",
        .@"or" => "or",
        .range_exclusive,
        .range_inclusive,
        => null,
    };
}

fn exprFormName(data: checked.CheckedExprData) []const u8 {
    return switch (data) {
        .list => "a list",
        .empty_list => "an empty list",
        .call, .dispatch_call, .type_dispatch_call => "a call",
        .closure => "a closure",
        .lambda => "a nested lambda",
        .lookup_external, .lookup_required => "a reference to another module",
        .for_ => "for",
        .return_ => "return",
        .break_ => "break",
        .expect, .expect_err => "expect",
        .interpolation => "string interpolation",
        .bytes_literal => "a byte-string literal",
        .row_coerce => "a widening to a wider tag union",
        .structural_eq, .method_eq => "an equality comparison",
        .structural_hash => "a derived hash",
        .run_low_level => "a compiler intrinsic",
        .ellipsis => "...",
        .runtime_error => "an expression that failed to compile",
        .pending,
        .numeral,
        .str_from_quote,
        .code_from_lambda,
        .str_segment,
        .str,
        .lookup_local,
        .tuple,
        .if_,
        .record,
        .empty_record,
        .block,
        .nominal,
        .binop,
        .unary_minus,
        .unary_not,
        .field_access,
        .tuple_access,
        .crash,
        .dbg,
        .anno_only,
        .hosted_lambda,
        .tag,
        .zero_argument_tag,
        .match_,
        => "this expression",
    };
}

/// Whether a binder's name is the one its author wrote.
///
/// A binder's name is read back from its region, which holds for a binding
/// written in the source and not for one the compiler introduced while
/// desugaring: the `Ok` binder `x ?? default` produces carries the whole
/// expression's region. A translator emits these names into its own target,
/// so a name that is not one is refused rather than carried.
/// The identifier an `as` pattern's region ends with.
///
/// The region covers the pattern being renamed as well, and only the name is
/// wanted. Scanning back over the characters a name may hold finds it without
/// the walk having to know what the pattern before it was written as.
/// The name inside a string pattern's `${name}`, or the text as it stands.
///
/// A capture's region is the whole interpolation, and `${x}` is no name a
/// target accepts, so the walk would invent one where the author wrote `x`.
fn interpolatedIdentifier(text: []const u8) []const u8 {
    if (text.len < 3) return text;
    if (text[0] != '$' or text[1] != '{' or text[text.len - 1] != '}') return text;
    return text[2 .. text.len - 1];
}

fn trailingIdentifier(text: []const u8) []const u8 {
    var start = text.len;
    while (start > 0 and isNameChar(text[start - 1])) start -= 1;
    return text[start..];
}

fn isNameChar(char: u8) bool {
    // `$` starts a `var`'s name, which Roc requires and which the
    // description carries the way it carries every other source spelling.
    return std.ascii.isAlphanumeric(char) or char == '_' or char == '!' or char == '$';
}

fn isWrittenName(text: []const u8) bool {
    if (text.len == 0) return false;
    // A literal pattern's region is its digits, and `380` is every bit a name
    // character, so the first one decides: no Roc name starts with a digit.
    if (std.ascii.isDigit(text[0])) return false;
    for (text) |char| {
        if (!isNameChar(char)) return false;
    }
    return true;
}

fn patternFormName(data: checked.CheckedPatternData) []const u8 {
    return switch (data) {
        .list => "a list pattern",
        .str_interpolation => "a string interpolation pattern",
        .runtime_error => "a pattern that failed to compile",
        // The checked artifact keeps an `as` binder without the identifier it
        // was written with, so there is no name for a translator to emit.
        .as => "an `as` pattern",
        .pending,
        .assign,
        .applied_tag,
        .nominal,
        .record_destructure,
        .tuple,
        .numeral_literal,
        .str_literal,
        .underscore,
        => "this pattern",
    };
}

fn statementFormName(data: checked.CheckedStatementData) []const u8 {
    return switch (data) {
        .expr => "a statement expression",
        .dbg => "dbg",
        .expect => "expect",
        .crash => "crash",
        .for_ => "for",
        .return_ => "return",
        .pending,
        .decl,
        .promoted_proc,
        .var_,
        .var_uninitialized,
        .reassign,
        .while_,
        .infinite_loop,
        .breakable_loop,
        .break_,
        .import_,
        .alias_decl,
        .where_alias_decl,
        .nominal_decl,
        .type_anno,
        .type_var_alias,
        .runtime_error,
        => "this statement",
    };
}

/// One staged site's result: the checked expression that carries the
/// description, and either the description or the reason the walk stopped.
pub const SiteOutcome = struct {
    expr: CheckedExprId,
    outcome: Outcome,
};

/// The checked body a constant template holds, or null when the compiler did
/// not fix a value for it.
pub fn constantBody(
    templates: *const checked.ConstTemplateTable,
    bodies: *const checked.CheckedConstBodyTable,
    const_ref: checked.ConstRef,
) ?CheckedExprId {
    const body = switch (templates.get(const_ref).state) {
        .eval_template => |eval| eval.body,
        // Evaluation replaces the eval template, and carries the body over so
        // a name that reads the constant still describes what was written.
        .stored_const => |stored| stored.body orelse return null,
        .reserved, .unimplemented => return null,
    };
    return bodies.get(body).body_expr;
}

/// A constant another module exports, resolved to what the walk reads.
pub const ForeignConstant = struct {
    module: ForeignModule,
    /// The checked expression the constant's value was written as.
    body: CheckedExprId,
};

/// A definition another module exports, resolved to what the walk reads.
pub const ForeignModule = struct {
    sources: Reifier.Sources,
    env: *const ModuleEnv,
};

/// A definition another module exports, resolved to what the walk reads.
pub const ForeignDefinition = struct {
    module: ForeignModule,
    /// The checked expression the definition's body is.
    body: CheckedExprId,
    /// The definition's own procedure template, which says whether it is
    /// generic without the walk having to read the owning module's tables.
    template: checked.CheckedProcedureTemplate,
};

/// A nominal named the way any module can read it: the content identity of the
/// module that declares it, and the declaration statement inside that module.
///
/// A `CheckedNominalType` names its module by an id of the store that holds
/// it, and a registry is keyed by the ids of the store beside it, so the two
/// meet on the identity bytes rather than on either store's ids. The
/// declaration is a statement index of the declaring module, which means the
/// same thing in every store.
pub const ForeignNominal = struct {
    module: *const [32]u8,
    source_decl: u32,
    /// The owner key a compiler builtin is registered under instead. It is a
    /// plain enum, so it already means the same thing in either store.
    builtin: ?static_dispatch.BuiltinOwner,
};

/// How the walk reaches a definition in another module.
///
/// Publication owns the import views, the export tables and the method
/// registries, so it answers this; the walk carries no import machinery of its
/// own. A name no module in reach exports and a method no module in reach
/// declares get the same null.
///
/// There are three questions because a name, a call and a method reach a
/// module by different routes. A staged site names a definition through an
/// import the author wrote, so the import index answers it. A call inside a
/// description reaches one through a binding the producer resolved, which
/// names the artifact rather than the import, and may name one this module
/// never imported itself. A method is declared against a nominal rather than
/// exported under a name, so the method registries answer it.
pub const ForeignLookup = struct {
    context: *const anyopaque,
    resolve: *const fn (
        context: *const anyopaque,
        import_idx: CIR.Import.Idx,
        target_node_idx: u32,
    ) ?ForeignDefinition,
    resolve_exported: *const fn (
        context: *const anyopaque,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignDefinition,
    /// A constant another module fixed, named by the ref the checker resolved
    /// the use to. A constant is reached by ref rather than by import index
    /// because the name that reads it may be written in a third module.
    resolve_constant: *const fn (
        context: *const anyopaque,
        const_ref: checked.ConstRef,
    ) ?ForeignConstant,
    /// What a nominal's declaration says about one method name: the target the
    /// checker recorded for it, or null when no module in reach declares it.
    ///
    /// This is the question the walk cannot answer from a body, because the
    /// compiler dispatches to a nominal's own method before it looks at the
    /// nominal's representation. The registries already carry it, so the walk
    /// asks rather than guesses: the target says written or derived, and
    /// guessing wrong would make a reified comparison disagree with Roc's.
    resolve_method: *const fn (
        context: *const anyopaque,
        owner: ForeignNominal,
        method: []const u8,
    ) ?static_dispatch.MethodTarget,
    /// The `to_inspect` a nominal declares when it is the override inspection
    /// uses, or null when inspection renders the value's default form.
    ///
    /// A `to_inspect` whose type does not qualify is an ordinary method that
    /// inspection ignores (design.md "Inspect Overrides"), and the registry
    /// records that decision per entry, so the walk reads it rather than
    /// judging the method's type itself.
    resolve_inspect_override: *const fn (
        context: *const anyopaque,
        owner: ForeignNominal,
    ) ?static_dispatch.MethodTarget,

    /// A lookup that reaches nothing, for a walk with no modules behind it.
    pub const none = ForeignLookup{
        .context = undefined,
        .resolve = resolveNothing,
        .resolve_exported = resolveNothingExported,
        .resolve_constant = resolveNothingConstant,
        .resolve_method = resolveNothingMethod,
        .resolve_inspect_override = resolveNothingInspectOverride,
    };

    fn resolveNothing(_: *const anyopaque, _: CIR.Import.Idx, _: u32) ?ForeignDefinition {
        return null;
    }

    fn resolveNothingExported(_: *const anyopaque, _: canonical.ArtifactRef, _: CIR.Def.Idx) ?ForeignDefinition {
        return null;
    }

    fn resolveNothingConstant(_: *const anyopaque, _: checked.ConstRef) ?ForeignConstant {
        return null;
    }

    fn resolveNothingMethod(_: *const anyopaque, _: ForeignNominal, _: []const u8) ?static_dispatch.MethodTarget {
        return null;
    }

    fn resolveNothingInspectOverride(_: *const anyopaque, _: ForeignNominal) ?static_dispatch.MethodTarget {
        return null;
    }

    /// The target a nominal's declaration names for one method.
    fn findMethod(
        self: ForeignLookup,
        owner: ForeignNominal,
        method: []const u8,
    ) ?static_dispatch.MethodTarget {
        return self.resolve_method(self.context, owner, method);
    }

    /// The inspect override a nominal's declaration names, if it has one.
    fn findInspectOverride(self: ForeignLookup, owner: ForeignNominal) ?static_dispatch.MethodTarget {
        return self.resolve_inspect_override(self.context, owner);
    }

    fn findConstant(self: ForeignLookup, const_ref: checked.ConstRef) ?ForeignConstant {
        return self.resolve_constant(self.context, const_ref);
    }

    fn find(
        self: ForeignLookup,
        import_idx: CIR.Import.Idx,
        target_node_idx: u32,
    ) ?ForeignDefinition {
        return self.resolve(self.context, import_idx, target_node_idx);
    }

    fn findExported(
        self: ForeignLookup,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignDefinition {
        return self.resolve_exported(self.context, artifact, def);
    }
};

/// One site's walk, across every module it reaches.
///
/// A description spans modules once a call can cross one, so three things
/// belong to the walk rather than to any one module's reader: the table being
/// built, the frame stack that records which definition calls which, and the
/// first construct that stopped it.
pub const Walk = struct {
    gpa: Allocator,
    store: *ConstStore,
    foreign: ForeignLookup,
    /// One reader per module the walk reaches. Pointers, so a reader stays put
    /// while a descent into another module adds one.
    readers: std.ArrayList(*Reifier) = .empty,
    /// Every definition the walk has described. One `Walk` serves every site
    /// of a module, so a callee two sites reach is described once and both
    /// tables name the same node.
    definitions: std.AutoArrayHashMapUnmanaged(DefinitionKey, Definition) = .empty,
    /// The callees of every definition the walk is inside, innermost frame
    /// last, with `frame_base` marking where the innermost frame starts.
    callees: std.ArrayList(DefinitionKey) = .empty,
    frame_base: usize = 0,
    rejection: ?Rejection = null,
    builtin_operators: ?BuiltinOperators = null,
    /// How many rows the walk has named after each spelling, so two that
    /// share one never take the same name.
    name_serials: std.StringHashMapUnmanaged(u32) = .empty,
    /// The `Str` node each text already has, so a description holds one node
    /// per distinct string rather than one per mention.
    str_nodes: collections.DenseMapUnmanaged(ConstBlobDataId, ConstNodeId) = .empty,

    pub fn init(gpa: Allocator, store: *ConstStore, foreign: ForeignLookup) Walk {
        return .{ .gpa = gpa, .store = store, .foreign = foreign };
    }

    pub fn deinit(self: *Walk) void {
        for (self.readers.items) |open| {
            open.deinit();
            self.gpa.destroy(open);
        }
        self.readers.deinit(self.gpa);
        for (self.definitions.values()) |definition| {
            if (definition.name) |name| self.gpa.free(name);
            self.gpa.free(definition.callees);
        }
        self.definitions.deinit(self.gpa);
        self.callees.deinit(self.gpa);
        var names = self.name_serials.keyIterator();
        while (names.next()) |name| self.gpa.free(name.*);
        self.name_serials.deinit(self.gpa);
        self.str_nodes.deinit(self.gpa);
    }

    /// The reader of one module, opened if the walk has not read it yet.
    ///
    /// A reader is per module because everything on it is: the stores it
    /// reads, and the type cache keyed by that module's type ids.
    pub fn reader(self: *Walk, module: ForeignModule) Allocator.Error!*Reifier {
        for (self.readers.items) |existing| {
            if (std.meta.eql(existing.artifact.bytes, module.sources.artifact.bytes)) return existing;
        }
        const opened = try self.gpa.create(Reifier);
        errdefer self.gpa.destroy(opened);
        opened.* = Reifier.init(self, module.sources, module.env);
        try self.readers.append(self.gpa, opened);
        return opened;
    }

    /// Builtin's operator names, resolved on the first builtin callee the
    /// walk meets, because every builtin callee names that one module.
    fn builtinOperators(self: *Walk, names: *const canonical.CanonicalNameStore) BuiltinOperators {
        if (self.builtin_operators) |resolved| return resolved;
        const resolved = BuiltinOperators.resolve(names);
        self.builtin_operators = resolved;
        return resolved;
    }

    /// The serial one row takes after its spelling, counted in the order the
    /// walk discovers them.
    fn nameSerial(self: *Walk, spelling: []const u8) Allocator.Error!u32 {
        const entry = try self.name_serials.getOrPut(self.gpa, spelling);
        if (entry.found_existing) {
            entry.value_ptr.* += 1;
        } else {
            entry.key_ptr.* = try self.gpa.dupe(u8, spelling);
            entry.value_ptr.* = 0;
        }
        return entry.value_ptr.*;
    }

    /// Start a site, so a site refused for one reason does not report the
    /// reason an earlier site was refused for.
    pub fn beginSite(self: *Walk) void {
        self.rejection = null;
    }

    fn closeFailedDefinition(self: *Walk, key: DefinitionKey) void {
        if (self.definitions.fetchSwapRemove(key)) |removed| {
            if (removed.value.name) |name| self.gpa.free(name);
            self.gpa.free(removed.value.callees);
        }
    }
};

/// The stores a module publishes the walk from, before they become views.
pub const LocalSources = struct {
    types: *const checked.CheckedTypeStore,
    bodies: *const checked.CheckedBodyStore,
    plans: *const static_dispatch.StaticDispatchPlanTable,
    names: *const canonical.CanonicalNameStore,
    artifact: checked.CheckedModuleArtifactKey,
    value_refs: *const checked.ResolvedValueRefTable,
    procedure_bindings: *const checked.TopLevelProcedureBindingTable,
    procedure_templates: *const checked.CheckedProcedureTemplateTable,
    const_templates: *const checked.ConstTemplateTable,
    const_bodies: *const checked.CheckedConstBodyTable,
    /// Where a site's `f` is read from. The checker records the site against a
    /// source variable, and only the module being published still has the
    /// index from a source variable to the checked type it solved for.
    site_types: *const checked.CheckedTypePublication,

    fn views(self: LocalSources) Reifier.Sources {
        return .{
            .types = self.types.view(),
            .bodies = self.bodies.view(),
            .plans = self.plans,
            .names = self.names,
            .artifact = self.artifact,
            .value_refs = self.value_refs,
            .procedure_bindings = self.procedure_bindings,
            .procedure_templates = self.procedure_templates,
            .const_templates = self.const_templates,
            .const_bodies = self.const_bodies,
        };
    }
};

/// Walk every function this module stages into `store`, one description per
/// recorded site. Publication runs this: the walk reads checked bodies and
/// solved types, and neither exists while the checker is still running.
///
/// `module` is the `TypedCIR.Module` being published, taken as `anytype` so the
/// reifier does not depend on the publication pipeline that calls it. The
/// caller owns the returned slice.
///
/// A site naming another module's definition is walked over that module's
/// published view, and the description it writes lands in this module's store
/// like any other. A template call is the one site with a foot in each: the
/// arguments are written here and the body is read there, so the local walk
/// describes the arguments and the foreign walk binds them.
pub fn reifyModuleSites(
    gpa: Allocator,
    store: *ConstStore,
    local: LocalSources,
    module: anytype,
    env: *const ModuleEnv,
    foreign: ForeignLookup,
) Allocator.Error![]SiteOutcome {
    const sites = env.store.codeReificationSites();
    if (sites.len == 0) return &.{};

    var walk = Walk.init(gpa, store, foreign);
    defer walk.deinit();
    const reifier = try walk.reader(.{ .sources = local.views(), .env = env });

    var results = std.ArrayList(SiteOutcome).empty;
    errdefer results.deinit(gpa);

    var call_args = std.ArrayList(CheckedExprId).empty;
    defer call_args.deinit(gpa);
    var call_values = std.ArrayList(Reifier.TemplateArg).empty;
    defer call_values.deinit(gpa);

    for (sites) |site| {
        // A template and the name a template call calls both stand for a
        // description built elsewhere, so nothing is walked for either: the
        // node keeps the empty description body copying left on it.
        switch (site.kind) {
            .template, .template_callee => continue,
            .named_function, .inline_lambda, .template_call => {},
        }
        const site_expr = local.bodies.exprIdAtRawNode(site.node_idx) orelse continue;
        const region = env.store.getRegionAt(@fromBackingInt(@intCast(site.node_idx)));
        walk.beginSite();
        const outcome: Outcome = switch (site.kind) {
            .named_function => try reifyNamedSite(&walk, reifier, module, local, site.node_idx, site.fn_var, region),
            // The lambda is the root, and the site is where it is written, so
            // the checked expression the node copied to is what the walk
            // reads, and the `f` beside it is the type to read it at.
            .inline_lambda => try reifier.reifyLambda(site_expr, .{
                .scheme = null,
                .in_block = true,
                .caller = reifier,
                .fixed = local.site_types.rootForSourceVar(
                    module,
                    ModuleEnv.varFrom(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(site.fn_var)))),
                ),
                .region = region,
            }),
            .template_call => try reifyTemplateSite(
                gpa,
                &walk,
                reifier,
                module,
                local,
                site.node_idx,
                region,
                &call_args,
                &call_values,
            ),
            .template, .template_callee => unreachable,
        };
        try results.append(gpa, .{ .expr = site_expr, .outcome = outcome });
    }

    return try results.toOwnedSlice(gpa);
}

/// A name in a `Code(f)` position, described from wherever it is defined and
/// at the types that position fixes it to.
///
/// A root generic in a variable `f` names describes at the type `f` gives it,
/// so one definition describes once per site type. A row is the one thing `f`
/// does not decide: it carries no row of its own by the time it gets here, and
/// a description has no form to put one in either way.
fn reifyNamedSite(
    walk: *Walk,
    reifier: *Reifier,
    module: anytype,
    local: LocalSources,
    node_idx: u32,
    fn_var: u32,
    region: base.Region,
) Allocator.Error!Outcome {
    const fixed = local.site_types.rootForSourceVar(module, ModuleEnv.varFrom(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(fn_var)))));
    const data = module.expr(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(node_idx)))).data;
    if (data == .e_lookup_external) {
        const external = data.e_lookup_external;
        const definition = walk.foreign.find(external.module_idx, external.target_node_idx) orelse
            return unreachableDefinition(region, "a function no module this one imports exports");
        const away = try walk.reader(definition.module);
        return away.reifyLambda(definition.body, .{
            .scheme = away.templateScheme(definition.template),
            .in_block = false,
            .caller = reifier,
            .fixed = fixed,
            .region = region,
        });
    }

    if (stagedDefinition(module, local, node_idx)) |staged| {
        return reifier.reifyLambda(staged.body, .{
            .scheme = reifier.templateScheme(staged.template),
            .in_block = false,
            .caller = reifier,
            .fixed = fixed,
            .region = region,
        });
    }

    // A local function the checker promoted is a procedure of its own. It
    // captures nothing, so it describes the way a top-level definition does,
    // through its own template and scheme.
    if (promotedDefinition(module, local, node_idx)) |promoted| {
        return reifier.reifyLambda(promoted.body, .{
            .scheme = reifier.templateScheme(promoted.template),
            .in_block = false,
            .caller = reifier,
            .fixed = fixed,
            .region = region,
        });
    }

    // Anything else the checker records here is a name a block binds to a
    // lambda. The lambda reads the block around it the way one written at the
    // site does, and describes at the site's `f` through the scheme the block
    // generalized it to.
    const lambda = blockLambda(module, local, node_idx) orelse
        return unreachableDefinition(region, "a function this module does not define");
    return reifier.reifyLambda(lambda, .{
        .scheme = reifier.localScheme(lambda),
        .in_block = true,
        .caller = reifier,
        .fixed = fixed,
        .region = region,
    });
}

/// The checked lambda a block binds the name at `node_idx` to: the binder's
/// defining statement holds it.
fn blockLambda(module: anytype, local: LocalSources, node_idx: u32) ?CheckedExprId {
    const data = module.expr(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(node_idx)))).data;
    if (data != .e_lookup_local) return null;
    const binder = local.bodies.patternBinderForSource(data.e_lookup_local.pattern_idx) orelse return null;
    const statement_id = local.bodies.patternBinder(binder).defining_statement orelse return null;
    const statement = local.bodies.statement(statement_id).data;
    if (statement != .decl) return null;
    return switch (local.bodies.expr(statement.decl.expr).data) {
        .lambda, .closure => statement.decl.expr,
        .pending,
        .numeral,
        .str_from_quote,
        .code_from_lambda,
        .str_segment,
        .str,
        .row_coerce,
        .bytes_literal,
        .lookup_local,
        .lookup_external,
        .lookup_required,
        .list,
        .empty_list,
        .tuple,
        .match_,
        .if_,
        .call,
        .record,
        .empty_record,
        .block,
        .tag,
        .nominal,
        .zero_argument_tag,
        .binop,
        .unary_minus,
        .unary_not,
        .field_access,
        .dispatch_call,
        .interpolation,
        .structural_eq,
        .structural_hash,
        .method_eq,
        .type_dispatch_call,
        .tuple_access,
        .runtime_error,
        .crash,
        .dbg,
        .expect_err,
        .expect,
        .ellipsis,
        .anno_only,
        .break_,
        .return_,
        .for_,
        .hosted_lambda,
        .run_low_level,
        => null,
    };
}

/// A call to a template, described with the call's arguments written into it.
fn reifyTemplateSite(
    gpa: Allocator,
    walk: *Walk,
    reifier: *Reifier,
    module: anytype,
    local: LocalSources,
    node_idx: u32,
    region: base.Region,
    args: *std.ArrayList(CheckedExprId),
    values: *std.ArrayList(Reifier.TemplateArg),
) Allocator.Error!Outcome {
    const call = try templateCall(gpa, module, local.bodies, node_idx, args, walk.foreign) orelse
        return unreachableDefinition(region, "a template this module cannot read");
    defer reifier.releaseTemplateArgs(values.items);

    // The arguments are written where the call is, so the local walk describes
    // them whether or not the template itself lives here.
    if (try reifier.reifyConstants(call.args, values, gpa)) |rejection| {
        return .{ .rejected = rejection };
    }

    const template = switch (call.template) {
        .here => |body| body,
        .away => |definition| {
            const away = try walk.reader(definition.module);
            return away.reifyTemplateCall(definition.body, values.items, region);
        },
    };
    return reifier.reifyTemplateCall(template, values.items, region);
}

fn unreachableDefinition(region: base.Region, detail: []const u8) Outcome {
    return .{ .rejected = .{
        .kind = .unresolved_reference,
        .region = region,
        .detail = detail,
    } };
}

/// One template call's pieces: the function called, and the arguments it fixes.
const TemplateCall = struct {
    /// Where the template's body is read from.
    template: union(enum) { here: CheckedExprId, away: ForeignDefinition },
    args: []const CheckedExprId,
};

/// The template a call site names, with the call's arguments.
///
/// `args` is built in the caller's scratch list, which every site reuses.
fn templateCall(
    gpa: Allocator,
    module: anytype,
    bodies: *const checked.CheckedBodyStore,
    node_idx: u32,
    args: *std.ArrayList(CheckedExprId),
    foreign: ForeignLookup,
) Allocator.Error!?TemplateCall {
    const expr_idx: CIR.Expr.Idx = @fromBackingInt(@intCast(node_idx));
    const data = module.expr(expr_idx).data;
    if (data != .e_call) return null;
    const call = data.e_call;

    const callee = module.expr(call.func).data;
    const template: @FieldType(TemplateCall, "template") = blk: {
        if (callee == .e_lookup_local) {
            const body = definitionBody(module, bodies, callee.e_lookup_local.pattern_idx) orelse return null;
            break :blk .{ .here = body };
        }
        if (callee == .e_lookup_external) {
            const external = callee.e_lookup_external;
            const definition = foreign.find(external.module_idx, external.target_node_idx) orelse return null;
            break :blk .{ .away = definition };
        }
        return null;
    };

    args.clearRetainingCapacity();
    for (module.moduleEnvConst().store.sliceExpr(call.args)) |arg_idx| {
        const arg = bodies.exprIdAtRawNode(@backingInt(arg_idx)) orelse return null;
        try args.append(gpa, arg);
    }
    return .{ .template = template, .args = args.items };
}

/// The checked body of the top-level definition this pattern binds.
fn definitionBody(
    module: anytype,
    bodies: *const checked.CheckedBodyStore,
    pattern_idx: CIR.Pattern.Idx,
) ?CheckedExprId {
    for (module.allDefs()) |def_idx| {
        const def = module.moduleEnvConst().store.getDef(def_idx);
        if (def.pattern != pattern_idx) continue;
        return bodies.exprIdAtRawNode(@backingInt(def.expr));
    }
    return null;
}

/// The checked lambda a staged site names in this module, and the procedure
/// template that says what the definition quantifies over.
///
/// Null where the site names something this module does not define as a
/// top-level procedure, which the site reports as a definition it cannot
/// reach.
const StagedDefinition = struct {
    body: CheckedExprId,
    template: checked.CheckedProcedureTemplate,
};

/// The procedure of the promoted local function the name at `node_idx`
/// binds, through the template publication recorded for its pattern.
fn promotedDefinition(module: anytype, local: LocalSources, node_idx: u32) ?StagedDefinition {
    const data = module.expr(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(node_idx)))).data;
    if (data != .e_lookup_local) return null;
    const ref = local.procedure_templates.lookupPromotedByPattern(data.e_lookup_local.pattern_idx) orelse return null;
    const template = local.procedure_templates.get(ref.template);
    const body = switch (template.body) {
        .checked_body => |body_id| local.bodies.body(body_id).root_expr,
        .intrinsic_wrapper, .entry_wrapper, .unimplemented => return null,
    };
    return .{ .body = body, .template = template };
}

fn stagedDefinition(module: anytype, local: LocalSources, node_idx: u32) ?StagedDefinition {
    const expr_idx: CIR.Expr.Idx = @fromBackingInt(@intCast(node_idx));
    const data = module.expr(expr_idx).data;
    if (data != .e_lookup_local) return null;
    const pattern_idx = data.e_lookup_local.pattern_idx;
    for (module.allDefs()) |def_idx| {
        const def = module.moduleEnvConst().store.getDef(def_idx);
        if (def.pattern != pattern_idx) continue;
        const body = local.bodies.exprIdAtRawNode(@backingInt(def.expr)) orelse return null;
        const ref = local.procedure_templates.lookupByDef(def_idx) orelse return null;
        return .{ .body = body, .template = local.procedure_templates.get(ref.template) };
    }
    return null;
}

test "the reifier's walk compiles" {
    // `reifyLambda` reaches every arm of the walk, so referencing it forces
    // analysis of the whole reifier without a checked artifact to run on.
    _ = &Reifier.init;
    _ = &Reifier.deinit;
    _ = &Reifier.reifyLambda;
}
