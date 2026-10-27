//! Reification: a checked function body becomes the normal form of
//! `roc-reify-normal-form.md`, written into the module's `ConstStore` as the
//! `Code` value `Builtin.roc` declares.
//!
//! The walk reads checked bodies, solved types and dispatch plans, and builds
//! every node through the reify builder (`reify.builder`), whose smart
//! constructors apply the local rules as the walk goes. A site's rows are its
//! root and every row the root's calls and closures reach; `code_emit` writes
//! them as `Code`'s backing, `{ graph, site, version }`.
//!
//! | Written | Built |
//! |---|---|
//! | a parameter, a binding, a `var` version | a reference to a row parameter or a node (N2 to N4) |
//! | an operator, a method or builtin call | `Prim`, named by owner and method (N1a) |
//! | a call of a definition | `Call` of the definition's row, walked once per key (N8a) |
//! | a function of another package | `Prim` by its qualified name; its body is not walked (N8h) |
//! | a lambda used as a value | `Closure` of its row, with its captures (N8b) |
//! | `if`, `match` | switches, first match wins; a construct that can exit is an exiting switch whose continuation is one join (N1c, N11f) |
//! | `for`, `while` | `ForRange`, `ForList` or `Loop`, with each carried `var` a slot (N11) |
//!
//! A construct the normal form cannot describe stops the walk and names itself,
//! so the diagnostic points at the expression the user wrote rather than at a
//! type.

const std = @import("std");
const collections = @import("collections");
const base = @import("base");
const reify = @import("reify");
const prims = reify.prims;

const CIR = @import("can").CIR;
const ModuleEnv = @import("can").ModuleEnv;
const View = @import("can").NodeStore.CodeReificationSite.View;
const canonical = @import("canonical_names.zig");
const checked = @import("checked_artifact.zig");
const const_store = @import("const_store.zig");
const code_emit = @import("code_emit.zig");
const static_dispatch = @import("static_dispatch_registry.zig");
const numeral = @import("types").numeral;

const Allocator = std.mem.Allocator;

const ConstNodeId = const_store.ConstNodeId;
const ConstStore = const_store.ConstStore;
const CheckedExprId = checked.CheckedExprId;
const CheckedPatternId = checked.CheckedPatternId;
const CheckedStatementId = checked.CheckedStatementId;
const CheckedTypeId = checked.CheckedTypeId;
const PatternBinderId = checked.PatternBinderId;

const ir = reify.ir;
const Ref = ir.Ref;
const RowId = ir.RowId;
const RegionId = ir.RegionId;
const TyId = ir.TyId;
const LitId = ir.LitId;
const Builder = reify.builder.Builder;
const Types = reify.types.Types;
const NameId = reify.types.NameId;

/// Why a function could not be described in the normal form.
pub const Rejection = struct {
    kind: Kind,
    region: base.Region,
    /// Names the offending construct, binding or type. Borrowed from a name
    /// store or a static string; valid as long as the artifact is.
    detail: []const u8,
    /// For `unresolved_type` met at a type variable: which variable, and
    /// where it stands. Null for every other refusal.
    open: ?OpenVariable = null,

    pub const Kind = enum {
        /// An expression form the normal form has no node for (`detail` names the form).
        unsupported_expression,
        /// A type the normal form has no type for (`detail` names the type constructor).
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
        /// Normalization reached a hard bound of the language version
        /// (`detail` names the bound), so the site is refused rather than
        /// normalized without end.
        bound_exceeded,
        /// A value the lambda reads at run time that its translator's
        /// `Code.Bound` cannot receive as an input slot (`detail` says why).
        input_not_bound,
    };
};

/// A type variable a refusal names, and where it stands.
pub const OpenVariable = struct {
    /// The name the annotation wrote for the variable, or null for one the
    /// checker introduced without a name.
    name: ?[]const u8,
    place: Place,
    cause: Cause,

    pub const Place = union(enum) {
        /// A parameter of the function, by its name, or by its position
        /// (from 1) for a pattern that binds no single name.
        parameter: union(enum) { name: []const u8, position: u32 },
        /// What the function returns.
        result,
        /// An expression inside the body.
        expression,
        /// The type a call or a `Code` position gives the function, which
        /// leaves one of its quantified variables unbound.
        use: enum { call, site },
    };

    pub const Cause = enum {
        /// An annotation wrote the variable, and the call or the `Code`
        /// position that uses the function does not fix it.
        use_leaves_open,
        /// An annotation wrote the variable, and nothing that uses the
        /// function fixes it.
        annotation_leaves_open,
        /// Checking inferred the variable, and nothing fixes it.
        inferred,
        /// Checking inferred the variable, and the call or the `Code`
        /// position that uses the function does not fix it.
        inferred_use_leaves_open,
    };
};

/// The two range methods a `for` over a range calls, resolved to ids once so
/// the walk compares ids and never text. `a..<b` reaches the walk as a call
/// to one of these, because that is what the checker resolves it to.
const RangeNames = struct {
    exclusive: ?canonical.MethodNameId,
    inclusive: ?canonical.MethodNameId,

    fn resolve(names: *const canonical.CanonicalNameStore) RangeNames {
        return .{
            .exclusive = names.lookupMethodName("range_exclusive_to"),
            .inclusive = names.lookupMethodName("range_inclusive_to"),
        };
    }

    /// Whether the range the method builds includes its end, or null where
    /// the method builds no range.
    fn inclusiveOf(self: RangeNames, method: canonical.MethodNameId) ?bool {
        if (self.exclusive) |id| {
            if (id == method) return false;
        }
        if (self.inclusive) |id| {
            if (id == method) return true;
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

/// The prefix every builtin's export name carries, which the owner and
/// method of its `Prim` follow (`Builtin.Num.F32.sin` is `Num.F32` and `sin`).
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
    /// it reads, rather than by taking what it captured as leading
    /// parameters. One lambda can be described each way: at a `Code` position
    /// or as a template's argument, and as a call.
    replayed: bool = false,
    /// The type this row delivers where it is not the one its lambda's own
    /// type gives: the nominal a lambda is read at, where the checker took
    /// the lambda's record or tag union for it.
    result: ?TyId = null,
    /// Which definitions this row's function parameters were fixed to,
    /// digested from the rows they name. Zero for a definition that takes no
    /// function parameter, so one body describes once.
    callees: [32]u8 = @as([32]u8, @splat(0)),
};

/// A definition some `Call` or `Closure` names: its row, and whether the walk
/// is still inside it. A call that reaches a definition the walk is inside
/// names its row and does not enter it again, which is what makes a recursive
/// call terminate.
const Definition = struct {
    /// Null only between the entry opening and the row beginning, while the
    /// walk reads the definition's signature.
    row: ?RowId = null,
    open: bool = true,
};

/// Either the `Code` value a site holds or the first construct that stopped
/// the walk.
pub const Outcome = union(enum) {
    reified: ConstNodeId,
    rejected: Rejection,
};

/// Reads a checked module and builds its sites' rows through the builder.
pub const Reifier = struct {
    gpa: Allocator,
    types: checked.CheckedTypeStoreView,
    bodies: checked.CheckedBodyStoreView,
    plans: *const static_dispatch.StaticDispatchPlanTable,
    names: *const canonical.CanonicalNameStore,
    artifact: checked.CheckedModuleArtifactKey,
    value_refs: *const checked.ResolvedValueRefTable,
    procedure_bindings: *const checked.TopLevelProcedureBindingTable,
    procedure_templates: *const checked.CheckedProcedureTemplateTable,
    callable_eval_templates: checked.CallableEvalTemplateTableView,
    const_templates: *const checked.ConstTemplateTable,
    const_bodies: *const checked.CheckedConstBodyTable,
    env: *const ModuleEnv,
    ranges: RangeNames,
    bool_tags: BoolTags,
    /// Binders visible in the row being built, innermost last. A lookup that
    /// misses this scope is a capture.
    scope: std.ArrayList(Binding) = .empty,
    /// What a root written at its site reads from the block around it, while
    /// that root is walked. Null everywhere else, a lifted row among them:
    /// a row takes what it captured as parameters.
    replay: ?*const Replay = null,
    /// The site's type for each checked type this reader has built. Cleared
    /// at every site, because each site has a type table of its own.
    ty_cache: collections.DenseMapUnmanaged(CheckedTypeId, TyId) = .empty,
    /// The types `tyOf` is part way through building. Roc reaches recursion
    /// only through a nominal, and `nominal_in_progress` closes that, so a type
    /// that reaches itself any other way has no description and is refused
    /// rather than recursed into forever.
    ///
    /// Keyed by the enclosing instantiation as well as the id, because a
    /// declaration's backing is one template every use shares: `Chain(F32)`
    /// and the `Chain(U16)` written inside it walk the same backing id under
    /// different bindings, and the second is not the first reaching itself.
    type_in_progress: std.AutoHashMapUnmanaged(TypeFrame, void) = .empty,
    /// Nominals that a `recursive` type built so far still refers to. A
    /// nominal closes its own, and a type left holding one names a nominal it
    /// does not contain, so what it means depends on where it sits rather than
    /// on its checked id alone.
    open_recursions: collections.DenseMapUnmanaged(CheckedTypeId, void) = .empty,
    /// The nominals `tyOf` is part way through building, each keyed by the
    /// declaration and what this use fixed its variables to, and each valued
    /// by the checked id the nominal being built carries.
    nominal_in_progress: std.AutoHashMapUnmanaged([32]u8, CheckedTypeId) = .empty,
    /// The innermost nominal instantiation `tyOf` is walking inside, zero
    /// where the walk is inside none.
    nominal_instance: [32]u8 = @splat(0),
    /// The constants the walk is part way through folding. A definition that
    /// reads itself is refused on the repeat rather than followed forever.
    folding: collections.DenseMapUnmanaged(CheckedExprId, void) = .empty,
    /// The loop whose body the walk is building, or null outside one. A
    /// `break` reads it for the slots it ends the loop with.
    loop: ?Loop = null,
    /// What the quantified variables of the definition being walked stand for.
    /// Empty while the walk is inside one that has none, which is every
    /// definition a monomorphic program writes.
    ///
    /// Borrowed from the call that fixed them, and restored on the way out, so
    /// one reader walks the same body once per instantiation.
    substitution: Substitution = .empty,
    /// The key of the instantiation `substitution` holds, zero where it is
    /// empty. A lambda written in the row extends it, so each instantiation
    /// of the definition keys its lambdas' rows apart.
    instance_key: [32]u8 = @splat(0),
    /// How often `substitution` has answered, so a type can tell whether it
    /// means anything beyond its own checked id.
    substitution_uses: u32 = 0,
    /// How the call that fixed this definition's quantified variables
    /// discharged its `where` obligations, in canonical evidence-param order.
    /// Empty while the walk is inside a definition with none.
    evidence: SuppliedEvidence = .{},
    /// Which definition each function parameter of this row was fixed to, by
    /// the call that wrote the row. Empty while the walk is inside a
    /// definition that takes no function parameter.
    bound: []const BoundCallee = &.{},
    /// The lambda whose parameters `bound` numbers, so a lambda nested inside
    /// that row binds its own parameters as parameters.
    bound_lambda: ?CheckedExprId = null,
    /// What each parametric nominal in the type being walked fixed its
    /// declared variables to, innermost last.
    nominal_args: Substitution = .empty,
    /// What relating each dispatch target publication selected to the
    /// callable it was selected for fixes this module's variables to (see
    /// `relateSelectedTargets`). A variable it answers for is no quantified
    /// variable of any definition, so the answer holds in every row.
    related: Substitution = .empty,
    /// Whether `related` has been computed.
    related_ready: bool = false,
    /// The dispatchers whose selected target does not fit the callable it
    /// was selected for: `x` in `|x| x * 2.U8`, whose default `Dec` has no
    /// `times` that takes a `U8`. Such a variable has no type to seal to.
    unfit: RowVars = .empty,
    /// What this reader shares with every other module's reader: the site's
    /// rows, who calls whom, and the first refusal.
    walk: *Walk,

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
    const Unfixed = struct {
        missing: []const u8,
        partial: []const u8,
        use: @FieldType(OpenVariable.Place, "use"),

        const call = Unfixed{
            .missing = "the type this call gives its callee",
            .partial = "a type variable this call does not fix",
            .use = .call,
        };
        const site = Unfixed{
            .missing = "the type of this Code position",
            .partial = "a type variable at this Code position",
            .use = .site,
        };
    };

    /// What one call supplied for its callee's `where` obligations, in
    /// canonical evidence-param order.
    ///
    /// `reader` is the module the call was written in, or null where no call
    /// supplied any. An entry may have been recorded in another module: one
    /// the call forwarded from its own definition's evidence is the entry the
    /// call that instantiated that definition supplied (see `supply`).
    const SuppliedEvidence = struct {
        reader: ?*Reifier = null,
        entries: []const SuppliedEntry = &.{},
    };

    /// How one obligation was discharged, beside what reads it.
    ///
    /// `reader` is the module that recorded the evidence: an evidence node id
    /// indexes that module's plan table, and the types recorded beside it are
    /// named in that module's store. `scope` is the evidence the walk held
    /// where it was recorded, which the nested evidence of a target it names
    /// forwards into.
    const SuppliedEntry = struct {
        reader: *Reifier,
        evidence: static_dispatch.CheckedEvidence,
        scope: SuppliedEvidence,
    };

    /// The definition a call's callee names: which one, and the reader of the
    /// module that defines it.
    const CalleeTarget = struct {
        key: DefinitionKey,
        reader: *Reifier,
        /// What this call fixes the callee's quantified variables to, or null
        /// when the callee has none. Owned by the call, and borrowed by the
        /// walk of the callee's body.
        instantiation: ?Instantiation = null,
        /// What this call supplies for the callee's `where` obligations.
        evidence: SuppliedEvidence = .{},
        /// What a lifted lambda captured, which its row takes as leading
        /// parameters and every call passes first. Empty for every other
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

    /// A template argument fixed to a value: the expression the call wrote,
    /// walked where the template's body reads the parameter.
    pub const TemplateConstant = struct {
        reader: *Reifier,
        expr: CheckedExprId,
    };

    /// What one template argument fixes its parameter to: a value, or the
    /// definition a function argument names.
    pub const TemplateArg = union(enum) {
        value: TemplateConstant,
        callee: CalleeTarget,
    };

    /// One function parameter of a callee, fixed to the definition the call
    /// passed for it.
    const BoundCallee = struct {
        param: Slot,
        target: CalleeTarget,

        /// What the definition fixes: a parameter, in the callee's own order,
        /// or a name a lifted lambda captured from a row where a call had
        /// fixed it. The lambda then names the definition, as the row did,
        /// and takes nothing for the name.
        const Slot = union(enum) {
            position: u32,
            capture: CheckedPatternId,
        };
    };

    /// What a call's callee is: a definition the walk builds a row for, a
    /// builtin, or a function of another package, which is a named
    /// primitive (N8h).
    const Callee = union(enum) {
        definition: CalleeTarget,
        /// A builtin, by its export name.
        provided: Provided,
        foreign: ForeignName,
        /// A function value the walk does not know, such as a parameter or
        /// one an `if` chooses: the call is an `Apply` (N8i), which
        /// simplifying resolves or the site is refused (N8j).
        value,
    };

    const Binding = struct {
        binder: PatternBinderId,
        kind: Kind,

        /// What a name in scope stands for.
        const Kind = union(enum) {
            /// A parameter, a binding or a `var` version: the value itself.
            value: Ref,
            /// A value a template call fixed, walked where it is read.
            constant: TemplateConstant,
            /// A function a block bound: a lambda written there, or one a
            /// call handed back. The payload is the expression that produced
            /// it, which a call lifts into a row and a read builds a closure
            /// of.
            function: CheckedExprId,
            /// A function parameter the call fixed to a definition, held as an
            /// index into the walk's bound callees. A call on the parameter
            /// names that definition, and the parameter itself is not in the
            /// row's signature.
            callee: u32,
        };
    };

    /// The block around a root that the root reads: a value it captured is
    /// the statement that produced it, walked where the root first reads it.
    /// A pure expression computes the same value on every call, so walking it
    /// there describes what the body reads.
    const Replay = struct {
        /// The root's region, which no replayed statement sits inside: a
        /// statement there is one the root's own walk binds.
        region: base.Region,
    };

    /// The parameters and body a lambda expression carries.
    const LambdaData = @FieldType(checked.CheckedExprData, "lambda");

    /// The loop whose body the walk is building.
    const Loop = struct {
        body: RegionId,
        /// Where the slots start among the body's parameters.
        slot_base: u30,
        /// Whether the first slot is the iterator of a general loop, which a
        /// `break` hands back as it stands.
        iterator: bool,
        /// The `var`s the slots carry, in slot order after the iterator.
        carried: []const PatternBinderId,
    };

    /// `error.Rejected` unwinds the walk, with the reason in the walk's
    /// `rejection`. `error.Diverged` says the region being built ended in a
    /// terminator, so the value the caller asked for does not exist on that
    /// path; whoever opened the region catches it.
    const Error = Allocator.Error || error{ Rejected, Diverged };

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
        /// What each top-level function binding that the compiler evaluates
        /// holds. An exact alias of a function, `same = add_one`, is one of
        /// these, and its template names the lookup the alias forwards to.
        callable_eval_templates: checked.CallableEvalTemplateTableView,
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
            .walk = walk,
            .types = sources.types,
            .bodies = sources.bodies,
            .plans = sources.plans,
            .names = sources.names,
            .artifact = sources.artifact,
            .value_refs = sources.value_refs,
            .procedure_bindings = sources.procedure_bindings,
            .procedure_templates = sources.procedure_templates,
            .callable_eval_templates = sources.callable_eval_templates,
            .const_templates = sources.const_templates,
            .const_bodies = sources.const_bodies,
            .env = env,
            .ranges = RangeNames.resolve(sources.names),
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
            .callable_eval_templates = artifact.callable_eval_templates.view(),
            .const_templates = &artifact.const_templates,
            .const_bodies = &artifact.checked_const_bodies,
        };
    }

    pub fn deinit(self: *Reifier) void {
        self.scope.deinit(self.gpa);
        self.ty_cache.deinit(self.gpa);
        self.type_in_progress.deinit(self.gpa);
        self.open_recursions.deinit(self.gpa);
        self.nominal_in_progress.deinit(self.gpa);
        self.nominal_args.deinit(self.gpa);
        self.related.deinit(self.gpa);
        self.unfit.deinit(self.gpa);
        self.folding.deinit(self.gpa);
    }

    /// The builder of the site being walked.
    fn bld(self: *Reifier) *Builder {
        return &self.walk.site.?.builder;
    }

    /// The type table of the site being walked.
    fn rt(self: *Reifier) *Types {
        return &self.walk.site.?.types;
    }

    /// The IR store of the site being walked.
    fn irs(self: *Reifier) *ir.Store {
        return &self.walk.site.?.store;
    }

    /// Describe the lambda at `root` as a `Code`: its row, and every row it
    /// reaches.
    ///
    /// `root` is a lambda of the module being walked, so a call can reach it
    /// and the site has to be able to hold it. `site` is what the site fixed
    /// the root to: its template, the reader of the module the site was
    /// written in, and the `f` of the surrounding `Code(f)`.
    pub fn reifyLambda(self: *Reifier, root: CheckedExprId, site: Site) Allocator.Error!Outcome {
        try self.walk.startSite();
        try site.caller.relateSelectedTargets();
        try self.relateSelectedTargets();
        return self.outcomeOf(self.rootSite(root, site), site.region);
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
        /// The expression the site is written at, which the checker keyed
        /// what the use copied the root's quantified variables to by. Null
        /// for a lambda written at the site.
        use: ?CheckedExprId = null,
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

    fn rootSite(self: *Reifier, root: CheckedExprId, site: Site) Error!RowId {
        // The root is a use of its own definition, so the site fixes its
        // quantified variables the way a call fixes a callee's. The walk of
        // the root's body borrows the substitution and finishes here.
        var instance = if (site.scheme) |scheme|
            try self.instantiationOf(scheme, site.caller, site.fixed, site.use, site.region, .site)
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
        return self.describeDefinition(key, instance, .{}, &.{}, at);
    }

    /// The site's `Code` value, or the reason the walk stopped.
    fn outcomeOf(self: *Reifier, result: Error!RowId, region: base.Region) Allocator.Error!Outcome {
        const row = result catch |err| switch (err) {
            error.Rejected => return .{ .rejected = self.walk.rejection.? },
            error.OutOfMemory => |e| return e,
            // A row ends where its body diverges, so no divergence reaches
            // past the row that caught it.
            error.Diverged => invariant("a divergence escaped the row that built it"),
        };
        const value = self.walk.finish(row, self.siteKey(region), region) catch |err| switch (err) {
            error.Rejected => return .{ .rejected = self.walk.rejection.? },
            error.OutOfMemory => |e| return e,
        };
        return .{ .reified = value };
    }

    /// The key `Code` carries for one site: the module and the site's place in
    /// it. Two sites with one normal form are equal by `Code.is_eq`, which
    /// skips the key, and still tell apart by it.
    fn siteKey(self: *Reifier, region: base.Region) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(&self.artifact.bytes);
        hasher.update(std.mem.asBytes(&region.start.offset));
        hasher.update(std.mem.asBytes(&region.end.offset));
        return hasher.final();
    }

    /// Check what each argument of a template call fixes, or say why one is
    /// not fixed. The caller releases `out` with `releaseTemplateArgs`.
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
                error.Diverged => invariant("a template argument diverged before any row was built"),
                error.OutOfMemory => |e| return e,
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

    /// A function argument binds the template's parameter to the definition
    /// it names, the way a call's function argument binds its callee's
    /// parameter. Any other argument is a constant form, walked where the
    /// template reads it.
    fn templateArg(self: *Reifier, arg_id: CheckedExprId) Error!TemplateArg {
        const arg = self.bodies.expr(arg_id);
        if (self.functionOf(arg.ty) == null) {
            if (!try self.isConstantForm(arg_id)) return self.rejectError(.argument_not_constant, arg.source_region, "");
            return .{ .value = .{ .reader = self, .expr = arg_id } };
        }
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
                .reader = self,
                .at = arg.ty,
            },
            .lookup_local => |local| {
                const binder = self.bodies.patternBinderForCheckedPattern(local.pattern) orelse
                    return self.rejectError(.unresolved_reference, region, "this argument");
                if (self.blockLambdaOf(binder)) |lambda| {
                    const binding = Binding{ .binder = binder, .kind = .{ .function = lambda } };
                    var lifted = (try self.liftedTarget(binding, arg.ty, arg_id, region)).definition;
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
    fn blockLambdaOf(self: *Reifier, binder: PatternBinderId) ?CheckedExprId {
        const statement_id = self.bodies.patternBinder(binder).defining_statement orelse return null;
        const statement = self.bodies.statement(statement_id).data;
        if (statement != .decl) return null;
        return if (self.lambdaOf(statement.decl.expr) != null) statement.decl.expr else null;
    }

    /// Describe the lambda `template` returns, with `values` written into it.
    ///
    /// `template` is the whole `Code`-returning function: its parameters are
    /// the compile-time ones, and the lambda it returns is what the stage
    /// reads. `values` is one per parameter, in order: a constant form, or
    /// the definition a function argument names.
    pub fn reifyTemplateCall(
        self: *Reifier,
        template: CheckedExprId,
        values: []const TemplateArg,
        region: base.Region,
    ) Allocator.Error!Outcome {
        try self.walk.startSite();
        try self.relateSelectedTargets();
        return self.outcomeOf(self.templateSite(template, values, region), region);
    }

    /// A template call's root row. The lambda a template returns is not a
    /// definition of any module, so nothing names it and no call reaches it.
    fn templateSite(
        self: *Reifier,
        template: CheckedExprId,
        values: []const TemplateArg,
        region: base.Region,
    ) Error!RowId {
        const lambda = try self.lambdaData(template);
        if (lambda.args.len != values.len) {
            return self.rejectError(.unsupported_expression, region, "a template called with the wrong number of arguments");
        }

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);

        // The site owns each callee; the walk borrows it, and a call on the
        // parameter copies it the way a call on a bound row parameter does.
        var bound = std.ArrayList(BoundCallee).empty;
        defer bound.deinit(self.gpa);
        for (lambda.args, values, 0..) |pattern_id, value, index| {
            switch (value) {
                .value => |constant| try self.bindName(pattern_id, .{ .constant = constant }, region),
                .callee => |target| {
                    try self.bindName(pattern_id, .{ .callee = @intCast(bound.items.len) }, region);
                    try bound.append(self.gpa, .{ .param = .{ .position = @intCast(index) }, .target = target });
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
        return self.lambdaRow(lambda.body, .in_scope, null, null);
    }

    /// Whether the walk describes this expression with no free names in it.
    ///
    /// A template's argument has to be one of these, because the value is
    /// walked where the template reads its parameter, in a row with none of
    /// the call's scope. A literal qualifies, and so does an aggregate every
    /// part of which does.
    fn isConstantForm(self: *Reifier, expr_id: CheckedExprId) Allocator.Error!bool {
        return switch (self.bodies.expr(expr_id).data) {
            // A literal of the author's own type describes as the conversion
            // call beside it, which reads no name.
            .numeral, .str_from_quote, .str_segment, .bytes_literal, .empty_list, .empty_record => true,
            .str => |segments| try self.everyPartIsConstant(segments),
            .list, .tuple => |items| try self.everyPartIsConstant(items),
            .record => |record| blk: {
                if (record.ext != null) break :blk false;
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

    // Rows //

    /// The parameters and body of the lambda an expression is, looking through
    /// a closure whose captures the row takes or the scope holds.
    fn lambdaData(self: *Reifier, expr_id: CheckedExprId) Error!LambdaData {
        const expr = self.bodies.expr(expr_id);
        return self.lambdaOf(expr_id) orelse self.rejectError(.unsupported_expression, expr.source_region, exprFormName(expr.data));
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

    /// Where a lambda's captures go.
    const CaptureRule = enum {
        /// The row is built where the scope already binds what the lambda
        /// captured: a template's parameters, or the block a root replays.
        in_scope,
        /// The row is built on its own, with none of the scope around it, so
        /// what the lambda captured arrives as a leading parameter and every
        /// call passes it first.
        parameter,
    };

    /// Which bound callee fixed one parameter of the row being walked, if the
    /// call fixed it at all.
    fn boundCallee(self: *Reifier, index: usize) ?u32 {
        for (self.bound, 0..) |entry, slot| {
            switch (entry.param) {
                .position => |position| if (position == index) return @intCast(slot),
                .capture => {},
            }
        }
        return null;
    }

    /// The bound callee a capture of the lambda being described names, as an
    /// index into the walk's bound callees.
    fn boundCapture(self: *Reifier, lambda: CheckedExprId, pattern: CheckedPatternId) ?u32 {
        if (self.bound_lambda != lambda) return null;
        return capturedCallee(self.bound, pattern);
    }

    /// The entry of `bound` that fixes a captured name, as an index into it.
    fn capturedCallee(bound: []const BoundCallee, pattern: CheckedPatternId) ?u32 {
        for (bound, 0..) |entry, slot| {
            switch (entry.param) {
                .capture => |captured| if (captured == pattern) return @intCast(slot),
                .position => {},
            }
        }
        return null;
    }

    /// The bound callee a name in scope stands for, when a call fixed it.
    fn calleeInScope(self: *Reifier, pattern: CheckedPatternId) ?u32 {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern) orelse return null;
        const binding = self.lookupBinding(binder) orelse return null;
        return switch (binding.kind) {
            .callee => |index| index,
            .value, .constant, .function => null,
        };
    }

    /// The function type of a lambda.
    ///
    /// A template's lambda is the node the `Code` landed on, so its own type is
    /// the `Code` rather than the function inside it. The lambda the closure
    /// wraps keeps the function type, and that is the one the signature reads.
    fn stagedFunctionTypeId(self: *Reifier, expr: checked.CheckedExpr) CheckedTypeId {
        if (self.functionOf(expr.ty) != null) return expr.ty;
        if (expr.data != .closure) return expr.ty;
        return self.bodies.expr(expr.data.closure.lambda).ty;
    }

    /// What a lambda captured from around itself, empty when it captured
    /// nothing. A plain lambda is the closure's body and holds none.
    fn capturesOf(self: *Reifier, expr_id: CheckedExprId) []const checked.CheckedCapture {
        const data = self.bodies.expr(expr_id).data;
        if (data != .closure) return &.{};
        return data.closure.captures;
    }

    /// Walk one definition's body into a row of its own, under an empty scope
    /// so it sees none of the caller's names.
    ///
    /// The entry opens before the walk, so a call that reaches this same
    /// definition names its row and stops rather than entering it a second
    /// time.
    fn describeDefinition(
        self: *Reifier,
        key: DefinitionKey,
        instance: ?Instantiation,
        supplied: SuppliedEvidence,
        bound: []const BoundCallee,
        /// The function type of a root written at its own site, whose node
        /// holds the `Code` rather than the function. Null for a definition,
        /// whose node holds its own type.
        at: ?CheckedTypeId,
    ) Error!RowId {
        std.debug.assert(std.meta.eql(key.artifact, self.artifact.bytes));
        try self.relateSelectedTargets();
        try self.walk.definitions.put(self.gpa, key, .{});

        const outer_substitution = self.substitution;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        const outer_replay = self.replay;
        const replay: Replay = .{ .region = self.bodies.expr(key.body).source_region };
        self.substitution = if (instance) |fixed| fixed.substitution else .empty;
        self.instance_key = key.instantiation;
        self.substitution_uses = 0;
        self.evidence = supplied;
        self.bound = bound;
        self.bound_lambda = key.body;
        self.replay = if (at != null) &replay else null;
        defer {
            self.substitution = outer_substitution;
            self.instance_key = outer_instance_key;
            self.substitution_uses = outer_uses;
            self.evidence = outer_evidence;
            self.bound = outer_bound;
            self.bound_lambda = outer_bound_lambda;
            self.replay = outer_replay;
        }

        const outer_scope = self.scope;
        const outer_loop = self.loop;
        self.scope = .empty;
        self.loop = null;
        defer {
            self.scope.deinit(self.gpa);
            self.scope = outer_scope;
            self.loop = outer_loop;
        }

        // A row takes what its lambda captured as leading parameters. A root
        // written at its site is the exception: its signature is the `f` the
        // site fixed, which has room for no added parameter, and what it
        // reads from around it is replayed where it reads it.
        const row = if (key.curried)
            try self.curriedLambdaRow(key.body, key)
        else if (at) |fn_ty|
            try self.lambdaRow(key.body, .in_scope, fn_ty, key)
        else
            try self.lambdaRow(key.body, .parameter, null, key);
        self.walk.definitions.getPtr(key).?.open = false;
        return row;
    }

    /// The row a lambda describes as.
    ///
    /// `at` is the function type to read the signature from, for a lambda
    /// whose node does not hold one. A lambda written at a `Code(f)` position
    /// is the case: its node holds the `Code`, so the walk is told the `f`.
    fn lambdaRow(
        self: *Reifier,
        expr_id: CheckedExprId,
        captures: CaptureRule,
        at: ?CheckedTypeId,
        key: ?DefinitionKey,
    ) Error!RowId {
        const expr = self.bodies.expr(expr_id);
        const region = expr.source_region;
        const lambda = try self.lambdaData(expr_id);
        const captured = self.capturesOf(expr_id);

        const fn_ty_id = at orelse self.stagedFunctionTypeId(expr);
        const staged_fn = self.functionOf(fn_ty_id) orelse
            return self.rejectError(.unsupported_type, region, "a reified value that is not a function");
        // A stage runs this description during `roc build`, where an effect has
        // nowhere to happen. `tyOf` refuses an effectful function everywhere
        // else; the staged lambda's own type is the one that never reaches it.
        if (staged_fn.kind == .effectful) return self.rejectError(.effect, region, "this function's own type is effectful (`=>`)");
        if (staged_fn.args.len != lambda.args.len) return self.rejectError(.unsupported_expression, region, "lambda");

        var params = std.ArrayList(TyId).empty;
        defer params.deinit(self.gpa);
        switch (captures) {
            .parameter => for (captured) |capture| {
                if (self.boundCapture(expr_id, capture.pattern) != null) continue;
                const pattern = self.bodies.pattern(capture.pattern);
                try params.append(self.gpa, try self.tyOf(pattern.ty, pattern.source_region));
            },
            // A capture of a name the scope already holds needs nothing at run
            // time: a template call fixed it, or the root replays the
            // statement that binds it. A name from outside the staged
            // function stays the refusal it has always been.
            .in_scope => for (captured) |capture| {
                if (self.capturedInScope(capture.pattern)) continue;
                if (self.replayStatement(capture.pattern) != null) continue;
                // A translator that returns a `Code.Bound` receives what the
                // body reads of it as an input slot (`inputSlot`).
                if (self.walk.inputs != null) continue;
                return self.rejectError(.capture, region, self.capturedName(capture.pattern));
            },
        }
        for (staged_fn.args, 0..) |param_ty, index| {
            // A parameter the call fixed to a definition is not a parameter of
            // the row: a call on it names that definition, and the call site
            // passes nothing for it.
            if (self.bound_lambda == expr_id and self.boundCallee(index) != null) continue;
            const place: TypePlace = .{ .parameter = .{ .reader = self, .pattern = lambda.args[index], .position = @intCast(index) } };
            try params.append(self.gpa, try self.placedTy(param_ty, region, place));
        }
        const own_result = try self.placedTy(staged_fn.ret, region, .result);
        const demanded = if (key) |k| k.result else null;
        const result = demanded orelse own_result;
        const lambdas = [_]CheckedExprId{expr_id};
        return self.buildRow(params.items, result, key, .{
            .demanded = demanded != null,
            .captures = if (captures == .parameter) captured else &.{},
            .lambdas = &lambdas,
            .body = lambda.body,
            .ret = staged_fn.ret,
        });
    }

    /// One row for a curried definition, with both lambdas' parameters
    /// gathered into one signature and the inner body as the body.
    ///
    /// A definition that hands back a function and the call that runs it are
    /// one row and one `Call`, the way the author reads them.
    fn curriedLambdaRow(self: *Reifier, expr_id: CheckedExprId, key: DefinitionKey) Error!RowId {
        const region = self.bodies.expr(expr_id).source_region;
        const outer = try self.lambdaData(expr_id);
        var params = std.ArrayList(TyId).empty;
        defer params.deinit(self.gpa);
        const lambdas = [_]CheckedExprId{ expr_id, outer.body };
        var ret: CheckedTypeId = undefined;
        for (lambdas) |lambda_id| {
            const lambda = try self.lambdaData(lambda_id);
            const fn_ty = self.functionOf(self.stagedFunctionTypeId(self.bodies.expr(lambda_id))) orelse
                return self.rejectError(.unsupported_type, region, "a reified value that is not a function");
            if (fn_ty.kind == .effectful) return self.rejectError(.effect, region, "this function's own type is effectful (`=>`)");
            if (fn_ty.args.len != lambda.args.len) return self.rejectError(.unsupported_expression, region, "lambda");
            for (fn_ty.args, 0..) |arg, index| {
                const place: TypePlace = .{ .parameter = .{ .reader = self, .pattern = lambda.args[index], .position = @intCast(params.items.len) } };
                try params.append(self.gpa, try self.placedTy(arg, region, place));
            }
            ret = fn_ty.ret;
        }
        const inner = try self.lambdaData(outer.body);
        return self.buildRow(params.items, try self.placedTy(ret, region, .result), key, .{
            .captures = self.capturesOf(expr_id),
            .lambdas = &lambdas,
            .body = inner.body,
            .ret = ret,
        });
    }

    /// What a row is built from: the captures it takes first, the lambdas
    /// whose parameters follow, outermost first, the body, and the checked
    /// result of the function type the row is built at.
    const RowParts = struct {
        /// Whether the row delivers a type other than the lambda's own
        /// (`DefinitionKey.result`).
        demanded: bool = false,
        captures: []const checked.CheckedCapture,
        lambdas: []const CheckedExprId,
        body: CheckedExprId,
        ret: CheckedTypeId,
    };

    /// Build one row, setting aside the row being built while it runs: a call
    /// reaches its callee in the middle of its caller's body.
    fn buildRow(self: *Reifier, param_tys: []const TyId, result: TyId, key: ?DefinitionKey, parts: RowParts) Error!RowId {
        const b = self.bld();
        const suspended: ?Builder.Suspended = if (b.building()) b.suspendRow() else null;
        errdefer if (suspended) |s| b.dropSuspended(s);
        const row = try b.beginRow(param_tys, result);
        if (key) |k| self.walk.definitions.getPtr(k).?.row = row;
        try self.walk.rows.append(self.gpa, row);
        defer _ = self.walk.rows.pop();

        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);
        // A row is no part of the first stage that reached it.
        const outer_stage = self.walk.stage_one;
        self.walk.stage_one = 0;
        defer self.walk.stage_one = outer_stage;
        // A lambda written inside a loop is a function of its own, so a
        // `break` in it has no loop to leave.
        const outer_loop = self.loop;
        self.loop = null;
        defer self.loop = outer_loop;

        var next: u30 = 0;
        for (parts.captures) |capture| {
            const region = self.bodies.pattern(capture.pattern).source_region;
            if (self.boundCapture(parts.lambdas[0], capture.pattern)) |slot| {
                try self.bindName(capture.pattern, .{ .callee = slot }, region);
                continue;
            }
            try self.bindName(capture.pattern, .{ .value = Ref.rowParam(next) }, region);
            next += 1;
        }
        for (parts.lambdas) |lambda_id| {
            const lambda = try self.lambdaData(lambda_id);
            for (lambda.args, 0..) |pattern_id, index| {
                if (self.bound_lambda == lambda_id) {
                    if (self.boundCallee(index)) |slot| {
                        try self.bindName(pattern_id, .{ .callee = slot }, self.bodies.pattern(pattern_id).source_region);
                        continue;
                    }
                }
                try self.bindPattern(pattern_id, Ref.rowParam(next));
                next += 1;
            }
        }
        std.debug.assert(next == param_tys.len);

        if (self.bodyValue(parts, result)) |value| {
            try b.endRow(.{ .value = &.{value} });
        } else |err| switch (err) {
            // The body ended the row itself, in `Return` or in an exiting switch.
            error.Diverged => {},
            error.Rejected, error.OutOfMemory => |e| return e,
        }
        if (suspended) |s| b.resumeRow(s);
        return row;
    }

    /// The value a row's body delivers. A body that composes a `?` result
    /// has a checked type of its own, narrower than the function's result,
    /// and delivers at the result (design.md "Try Return-Row Composition").
    fn bodyValue(self: *Reifier, parts: RowParts, result: TyId) Error!Ref {
        if (parts.demanded) return self.conformed(try self.exprAt(parts.body, result), result);
        if (parts.ret == self.bodies.expr(parts.body).ty) return self.exprRef(parts.body);
        return self.exprAt(parts.body, result);
    }

    /// The row a callee describes as, walked on the first call that reaches
    /// it. A call that reaches a row the walk is inside marks every row from
    /// that one to this one recursive, which each is: it reaches itself.
    ///
    /// Takes the callee's instantiation and bound callees, which the walk of
    /// its body borrows and this frees.
    fn calledRow(self: *Reifier, callee: CalleeTarget) Error!RowId {
        var target = callee;
        defer if (target.instantiation) |*instance| instance.substitution.deinit(self.gpa);
        defer self.releaseBound(target.bound);
        if (self.walk.definitions.get(target.key)) |existing| {
            const row = existing.row orelse invariant("a call reached a definition before its row began");
            if (existing.open) self.walk.markRecursive(row);
            return row;
        }
        return target.reader.describeDefinition(target.key, target.instantiation, target.evidence, target.bound, target.at);
    }

    /// A lambda written where a value stands: a closure of its row, over what
    /// it captured (N8b).
    ///
    /// `at` is the function type the lambda is read at. The checker takes a
    /// record or a tag union for the nominal that declares it, so a lambda
    /// that builds one and is read at a function of the nominal delivers the
    /// nominal: its row is built at it.
    fn closureAt(self: *Reifier, expr_id: CheckedExprId, at: ?TyId) Error!Ref {
        const expr = self.bodies.expr(expr_id);
        const fn_ty = try self.tyOf(self.stagedFunctionTypeId(expr), expr.source_region);
        var target = try self.enclosedLambda(expr_id, null, self.capturesOf(expr_id));
        target.key.result = self.readAsNominal(fn_ty, at);
        const closure_ty = if (target.key.result != null) at.? else fn_ty;
        if (self.walk.stage_one == 0) return self.closureOf(target, closure_ty);
        // A lambda a first stage writes may be applied before the stage ends,
        // where the walk stands, so its target is kept beside its row.
        const kept = try self.boundTarget(target);
        errdefer Walk.freeTarget(self.gpa, kept);
        const closure = try self.closureOf(target, closure_ty);
        const known = self.bld().knownClosure(closure) orelse invariant("a lambda's closure is a Closure node");
        const previous = try self.walk.closure_targets.fetchPut(self.gpa, known.row, kept);
        if (previous) |old| Walk.freeTarget(self.gpa, old.value);
        return closure;
    }

    /// The target of a lambda written in the row being walked.
    ///
    /// The lambda is part of the definition that row describes, so it
    /// describes under the instantiation the row does: what the call fixed
    /// the definition's quantified variables to, and how it discharged its
    /// `where` obligations. `local` is what a lookup fixed the variables of a
    /// lambda its block generalized to, and it extends the row's own. Such a
    /// lambda has a dispatch scope of its own, so the row's evidence is not
    /// its evidence. Takes `local`.
    fn enclosedLambda(
        self: *Reifier,
        expr_id: CheckedExprId,
        local: ?Instantiation,
        captures: []const checked.CheckedCapture,
    ) Error!CalleeTarget {
        const evidence: SuppliedEvidence = if (local == null) self.evidence else .{};
        var instance = local;
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);

        // A name a call fixed to a definition is that definition here too,
        // so the lambda's row names it rather than taking a function value.
        var bound = std.ArrayList(BoundCallee).empty;
        errdefer {
            self.releaseBound(bound.items);
            bound.deinit(self.gpa);
        }
        for (captures) |capture| {
            const index = self.calleeInScope(capture.pattern) orelse continue;
            try bound.append(self.gpa, .{ .param = .{ .capture = capture.pattern }, .target = try self.boundTarget(self.bound[index].target) });
        }
        if (self.substitution.count() != 0) {
            var merged = try self.substitution.clone(self.gpa);
            errdefer merged.deinit(self.gpa);
            var hasher = std.crypto.hash.Blake3.init(.{});
            hasher.update(&self.instance_key);
            if (instance) |*fixed| {
                var entries = fixed.substitution.iterator();
                while (entries.next()) |entry| try merged.put(self.gpa, entry.key_ptr.*, entry.value_ptr.*);
                hasher.update(&fixed.key);
                fixed.substitution.deinit(self.gpa);
            }
            var key: [32]u8 = undefined;
            hasher.final(&key);
            instance = .{ .substitution = merged, .key = key };
        }
        const callees = if (bound.items.len == 0) @as([32]u8, @splat(0)) else boundCalleesKey(bound.items);
        return .{
            .key = .{
                .artifact = self.artifact.bytes,
                .body = expr_id,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
                .callees = callees,
            },
            .reader = self,
            .instantiation = instance,
            .evidence = evidence,
            .captures = captures,
            .bound = try bound.toOwnedSlice(self.gpa),
        };
    }

    /// A closure of a callee's row. What the callee captured is read here,
    /// where the lambda was written, before the row is built.
    fn closureOf(self: *Reifier, target: CalleeTarget, fn_ty: TyId) Error!Ref {
        var values = std.ArrayList(Ref).empty;
        defer values.deinit(self.gpa);
        for (target.captures) |capture| {
            if (capturedCallee(target.bound, capture.pattern) != null) continue;
            const pattern = self.bodies.pattern(capture.pattern);
            try values.append(self.gpa, try self.lookupRef(capture.pattern, null, pattern.ty, null, null, pattern.source_region));
        }
        const row = try self.calledRow(target);
        return self.bld().closure(row, values.items, fn_ty);
    }

    /// The result type `at` gives a function of type `own`, where `at` reads
    /// the nominal over the type `own` delivers, and null for any other `at`.
    fn readAsNominal(self: *Reifier, own: TyId, at: ?TyId) ?TyId {
        const types = self.rt();
        const wanted = at orelse return null;
        const own_ret = switch (types.get(own)) {
            .func => |function| function.ret,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive => return null,
        };
        const wanted_ret = switch (types.get(wanted)) {
            .func => |function| function.ret,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive => return null,
        };
        if (wanted_ret == own_ret) return null;
        return switch (types.get(wanted_ret)) {
            .nominal => |nominal| if (nominal.backing == own_ret) wanted_ret else null,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => null,
        };
    }

    /// `value` at the nominal `ty` where `ty` is the nominal over its type.
    fn conformed(self: *Reifier, value: Ref, ty: TyId) Error!Ref {
        const types = self.rt();
        if (self.irs().refTy(self.bld().row, value) == ty) return value;
        return switch (types.get(ty)) {
            .nominal => |nominal| if (nominal.backing == self.irs().refTy(self.bld().row, value)) self.bld().wrap(ty, value) else value,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => value,
        };
    }

    // First stage //

    /// Whether this reader's walk is inside the first stage of an
    /// interpolated literal, at a call whose result holds a function. Such a
    /// call is walked where it stands, because a node named for it would give
    /// back a function that nothing can apply.
    fn walksInline(self: *Reifier, result_ty: CheckedTypeId, region: base.Region) Error!bool {
        if (self.walk.stage_one == 0) return false;
        return self.holdsFunction(try self.tyOf(result_ty, region));
    }

    /// Whether a value of `ty` holds a function.
    fn holdsFunction(self: *Reifier, ty: TyId) bool {
        const types = self.rt();
        return switch (types.get(ty)) {
            .func => true,
            .bool_, .str, .int, .float, .dec, .opaque_, .recursive => false,
            .list => |elem| self.holdsFunction(elem),
            .nominal => |nominal| self.holdsFunction(nominal.backing),
            .record, .tuple, .tag_union => |span| {
                for (types.memberSlice(span)) |member| {
                    for (types.tySlice(member.tys)) |item| if (self.holdsFunction(item)) return true;
                }
                return false;
            },
        };
    }

    /// A definition's body, walked where the call stands with its parameters
    /// bound to `args`, as a lifted lambda's body is with its captures first.
    /// Takes the callee's instantiation and bound callees.
    fn inlineCall(self: *Reifier, callee: CalleeTarget, args: []const Ref, at: ?TyId, region: base.Region) Error!Ref {
        var target = callee;
        defer if (target.instantiation) |*instance| instance.substitution.deinit(self.gpa);
        defer self.releaseBound(target.bound);
        return target.reader.inlineBody(target, args, at, region);
    }

    /// `at` is the type the site reads the value at, where it is not the
    /// definition's own.
    fn inlineBody(self: *Reifier, target: CalleeTarget, args: []const Ref, at: ?TyId, region: base.Region) Error!Ref {
        std.debug.assert(std.meta.eql(target.key.artifact, self.artifact.bytes));
        const lambda_id = target.key.body;
        const lambda = try self.lambdaData(lambda_id);
        // A body that reads itself, or that can leave the row it is walked in,
        // has no value to walk to.
        if (self.folding.contains(lambda_id)) return self.rejectError(.unsupported_expression, region, "a conversion that calls itself");
        if (self.transfers(lambda.body)) return self.rejectError(.unsupported_expression, region, "a conversion that leaves its body early");
        const fn_ty = self.functionOf(self.stagedFunctionTypeId(self.bodies.expr(lambda_id))) orelse
            return self.rejectError(.unsupported_type, region, "a reified value that is not a function");
        try self.relateSelectedTargets();
        try self.folding.put(self.gpa, lambda_id, {});
        defer _ = self.folding.remove(lambda_id);

        const outer_substitution = self.substitution;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        const outer_replay = self.replay;
        self.substitution = if (target.instantiation) |fixed| fixed.substitution else .empty;
        self.instance_key = target.key.instantiation;
        self.substitution_uses = 0;
        self.evidence = target.evidence;
        self.bound = target.bound;
        self.bound_lambda = lambda_id;
        self.replay = null;
        defer {
            self.substitution = outer_substitution;
            self.instance_key = outer_instance_key;
            self.substitution_uses = outer_uses;
            self.evidence = outer_evidence;
            self.bound = outer_bound;
            self.bound_lambda = outer_bound_lambda;
            self.replay = outer_replay;
        }
        // The body sees none of the names around the call.
        const outer_scope = self.scope;
        const outer_loop = self.loop;
        self.scope = .empty;
        self.loop = null;
        defer {
            self.scope.deinit(self.gpa);
            self.scope = outer_scope;
            self.loop = outer_loop;
        }

        var next: usize = 0;
        for (target.captures) |capture| {
            const capture_region = self.bodies.pattern(capture.pattern).source_region;
            if (self.boundCapture(lambda_id, capture.pattern)) |slot| {
                try self.bindName(capture.pattern, .{ .callee = slot }, capture_region);
                continue;
            }
            try self.bindName(capture.pattern, .{ .value = args[next] }, capture_region);
            next += 1;
        }
        for (lambda.args, 0..) |pattern_id, index| {
            if (self.boundCallee(index)) |slot| {
                try self.bindName(pattern_id, .{ .callee = slot }, self.bodies.pattern(pattern_id).source_region);
                continue;
            }
            try self.bindPattern(pattern_id, args[next]);
            next += 1;
        }
        std.debug.assert(next == args.len);

        const result = at orelse target.key.result orelse try self.tyOf(fn_ty.ret, region);
        const walked = if (at == null and target.key.result == null and fn_ty.ret == self.bodies.expr(lambda.body).ty)
            self.exprRef(lambda.body)
        else
            self.exprAt(lambda.body, result);
        const value = walked catch |err| switch (err) {
            error.Diverged => invariant("a body the scan found no exit in diverged"),
            error.Rejected, error.OutOfMemory => |e| return e,
        };
        return if (at != null or target.key.result != null) self.conformed(value, result) else value;
    }

    /// The call of a function value that a first stage wrote as a lambda,
    /// walked where it stands, or null for any other function value.
    fn appliedInline(self: *Reifier, f: Ref, args: []const Ref, at: TyId, region: base.Region) Error!?Ref {
        if (self.walk.stage_one == 0) return null;
        const known = self.bld().knownClosure(f) orelse return null;
        const registered = self.walk.closure_targets.get(known.row) orelse return null;
        const all = try self.gpa.alloc(Ref, known.captures.len + args.len);
        defer self.gpa.free(all);
        @memcpy(all[0..known.captures.len], known.captures);
        @memcpy(all[known.captures.len..], args);
        return try self.inlineCall(try self.boundTarget(registered), all, at, region);
    }

    // Scope //

    fn lookupBinding(self: *Reifier, binder: PatternBinderId) ?Binding {
        var index = self.scope.items.len;
        while (index > 0) {
            index -= 1;
            if (self.scope.items[index].binder == binder) return self.scope.items[index];
        }
        return null;
    }

    /// Put the binder an `assign` pattern binds in scope. Any other pattern is
    /// refused: only a name can stand for what `kind` holds.
    fn bindName(self: *Reifier, pattern_id: CheckedPatternId, kind: Binding.Kind, region: base.Region) Error!void {
        const binder = switch (self.bodies.pattern(pattern_id).data) {
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
        try self.scope.append(self.gpa, .{ .binder = binder, .kind = kind });
    }

    fn bindValue(self: *Reifier, binder: PatternBinderId, value: Ref) Allocator.Error!void {
        try self.scope.append(self.gpa, .{ .binder = binder, .kind = .{ .value = value } });
    }

    /// End a scope that did not branch: its own bindings go, and each `var`
    /// of the enclosing scope keeps the version the scope left it at, which
    /// is what a read after it sees.
    fn leaveScope(self: *Reifier, base_len: usize) Allocator.Error!void {
        var kept = std.ArrayList(Binding).empty;
        defer kept.deinit(self.gpa);
        var index = self.scope.items.len;
        while (index > base_len) {
            index -= 1;
            const binding = self.scope.items[index];
            if (binding.kind != .value) continue;
            if (!self.boundBefore(binding.binder, base_len)) continue;
            const seen = for (kept.items) |k| {
                if (k.binder == binding.binder) break true;
            } else false;
            if (!seen) try kept.append(self.gpa, binding);
        }
        self.scope.shrinkRetainingCapacity(base_len);
        var k = kept.items.len;
        while (k > 0) {
            k -= 1;
            try self.scope.append(self.gpa, kept.items[k]);
        }
    }

    /// Whether `binder` is bound in the first `len` entries of the scope.
    fn boundBefore(self: *Reifier, binder: PatternBinderId, len: usize) bool {
        for (self.scope.items[0..len]) |binding| {
            if (binding.binder == binder) return true;
        }
        return false;
    }

    /// Whether a capture names something the scope already binds.
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

    /// The statement that binds a name the root reads from the block around
    /// it, or null where nothing replays it: no root is being walked, or the
    /// statement sits inside the root and the walk binds it there.
    fn replayStatement(self: *Reifier, pattern_id: CheckedPatternId) ?CheckedStatementId {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse return null;
        return self.replayStatementOf(binder);
    }

    fn replayStatementOf(self: *Reifier, binder: PatternBinderId) ?CheckedStatementId {
        const replay = self.replay orelse return null;
        const statement_id = self.bodies.patternBinder(binder).defining_statement orelse return null;
        const statement = self.bodies.statement(statement_id).source_region;
        if (statement.start.offset >= replay.region.start.offset and statement.end.offset <= replay.region.end.offset) return null;
        return statement_id;
    }

    /// Resolve a name the root reads from the block around it: the statement
    /// that binds it is walked here, where the root first reads it, and binds
    /// its names in the scope that reads them. A statement reads only what
    /// the statements before it bind, so a replay that reads another name
    /// replays that statement first.
    fn replayBinding(self: *Reifier, binder: PatternBinderId) Error!?Binding {
        const statement_id = self.replayStatementOf(binder) orelse return null;
        const decl = switch (self.bodies.statement(statement_id).data) {
            .decl => |decl| decl,
            // A promoted local function has no value to replay: every use of
            // its name resolves to its procedure.
            .promoted_proc,
            .pending,
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
            .break_,
            .return_,
            .import_,
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            .runtime_error,
            => return null,
        };
        try self.declStatement(decl.pattern, decl.expr);
        return self.lookupBinding(binder);
    }

    /// The name the canonicalizer recorded on the pattern that binds `binder`,
    /// read from the ident store of the module that owns it.
    fn binderName(self: *Reifier, binder: PatternBinderId) []const u8 {
        // A source binding pattern always records its identifier; only a
        // literal pattern's matched-value binder has none, and no capture,
        // parameter or exported function names one.
        const name = self.bodies.patternBinder(binder).name orelse unreachable; // a source binding pattern always records its identifier (see above)
        return self.env.getIdentText(name);
    }

    // Values //

    /// Bind the names an irrefutable pattern binds, each to the part of
    /// `value` it names: a record's `Field`, a tuple's `Index`, a single
    /// variant's `Payload` (N1f). A pattern that can fail belongs to a
    /// `match`, and is refused here.
    fn bindPattern(self: *Reifier, pattern_id: CheckedPatternId, value: Ref) Error!void {
        const pattern = self.bodies.pattern(pattern_id);
        const region = pattern.source_region;
        const b = self.bld();
        switch (pattern.data) {
            .assign => |binder| try self.bindValue(binder, value),
            .underscore => {},
            .as => |renamed| {
                try self.bindValue(renamed.binder, value);
                try self.bindPattern(renamed.pattern, value);
            },
            .record_destructure => |destructs| {
                const record = try self.readable(value);
                for (destructs) |destruct| {
                    const inner = switch (destruct.kind) {
                        .required, .sub_pattern => |inner| inner,
                        // A `..` that binds nothing stands for the fields the
                        // pattern did not name. One that binds a name binds a
                        // record built out of what is left, which is not a read.
                        .rest => |inner| {
                            if (self.bodies.pattern(inner).data == .underscore) continue;
                            return self.rejectError(.unsupported_expression, region, "a record pattern whose `..` binds a name");
                        },
                    };
                    const index = try self.fieldIndex(record, self.names.recordFieldLabelText(destruct.label), region);
                    try self.bindPattern(inner, try b.field(record, index));
                }
            },
            .tuple => |items| {
                const tuple = try self.readable(value);
                for (items, 0..) |item, position| {
                    if (self.bodies.pattern(item).data == .underscore) continue;
                    try self.bindPattern(item, try b.index(tuple, @intCast(position)));
                }
            },
            .nominal => |nominal| try self.bindPattern(nominal.backing_pattern, try self.unwrapOnce(value)),
            .applied_tag => |applied| {
                const subject = try self.readable(value);
                const union_ty = self.irs().refTy(b.row, subject);
                const variants = switch (self.rt().get(union_ty)) {
                    .tag_union => |span| span,
                    .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return self.rejectError(.unsupported_expression, region, "a destructuring pattern that can fail"),
                };
                if (variants.len != 1) return self.rejectError(.unsupported_expression, region, "a destructuring pattern that can fail");
                const tag_name = try self.tagName(union_ty, self.names.tagLabelText(applied.name), region);
                for (applied.args, 0..) |arg, k| try self.bindPattern(arg, try b.payload(subject, tag_name, @intCast(k)));
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

    /// `value` with every nominal around it unwrapped, which is what a field,
    /// index or tag read reads.
    fn readable(self: *Reifier, value: Ref) Error!Ref {
        var current = value;
        while (true) {
            switch (self.rt().get(self.irs().refTy(self.bld().row, current))) {
                .nominal => current = try self.bld().unwrap(current),
                .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => return current,
            }
        }
    }

    /// `value` with one nominal around it unwrapped, or `value` where it is
    /// not a nominal: the backing a nominal pattern matches.
    fn unwrapOnce(self: *Reifier, value: Ref) Error!Ref {
        return switch (self.rt().get(self.irs().refTy(self.bld().row, value))) {
            .nominal => self.bld().unwrap(value),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => value,
        };
    }

    /// The position of the field named `name` in a record value's type.
    fn fieldIndex(self: *Reifier, record: Ref, name: []const u8, region: base.Region) Error!u32 {
        const ty = self.irs().refTy(self.bld().row, record);
        return self.memberIndex(ty, name) orelse self.rejectError(.unsupported_type, region, "a field the record's type does not have");
    }

    /// The name of the tag `name`, which the union `union_ty` has.
    fn tagName(self: *Reifier, union_ty: TyId, name: []const u8, region: base.Region) Error!NameId {
        const id = self.rt().findName(name) orelse return self.rejectError(.unsupported_type, region, "a tag the union does not have");
        if (self.rt().memberIndex(union_ty, id) == null) return self.rejectError(.unsupported_type, region, "a tag the union does not have");
        return id;
    }

    /// The names of the members of the tag union `union_ty`, in name order.
    /// The caller frees the result.
    fn memberNames(self: *Reifier, union_ty: TyId, region: base.Region) Error![]NameId {
        const types = self.rt();
        const span = switch (types.get(union_ty)) {
            .tag_union => |span| span,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a tag union operand"),
        };
        const members = types.memberSlice(span);
        const names = try self.gpa.alloc(NameId, members.len);
        for (members, names) |member, *name| name.* = member.name;
        return names;
    }

    fn memberIndex(self: *Reifier, ty: TyId, name: []const u8) ?u32 {
        const types = self.rt();
        const span = switch (types.get(ty)) {
            .record, .tag_union => |span| span,
            .bool_, .str, .int, .float, .dec, .tuple, .list, .nominal, .func, .opaque_, .recursive => return null,
        };
        const id = types.findName(name) orelse return null;
        for (types.memberSlice(span), 0..) |member, index| {
            if (member.name == id) return @intCast(index);
        }
        return null;
    }

    fn exprRef(self: *Reifier, expr_id: CheckedExprId) Error!Ref {
        return self.exprAs(expr_id, null);
    }

    /// The value of `expr_id` built at `at`, the type its position fixes.
    ///
    /// The two differ where a value is used at a wider tag union than its
    /// own: a lambda body composes a `?` result, whose error row holds every
    /// tag of the body's own (design.md "Try Return-Row Composition"), or the
    /// checker stamped a `row_coerce` (design.md "Row Coercion Primitive").
    /// A constructor and a call build at `at` directly, and a branching
    /// construct or block builds each of its values there. Any other value
    /// whose own type is not `at` is returned as it is: a tag has the same
    /// name at every union, so the value conforms to `at` (the verifier
    /// checks it).
    fn exprAt(self: *Reifier, expr_id: CheckedExprId, at: TyId) Error!Ref {
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        var here = [1]reify.provenance.OriginId{try self.walk.originAt(self.artifact, region)};
        const outer = self.bld().origins;
        self.bld().origins = &here;
        defer self.bld().origins = outer;
        return switch (expr_data.data) {
            .tag, .zero_argument_tag, .nominal => self.exprAs(expr_id, at),
            .row_coerce => |coerce| self.exprAt(coerce.value, at),
            // A call whose result is read at a wider union has that union as its type.
            .call => |call| self.callExpr(call.func, call.args, expr_data.ty, at, region),
            // A constant a name folds to is built at `at`.
            .lookup_local => |lookup| self.lookupRef(lookup.pattern, lookup.resolved, expr_data.ty, expr_id, at, region),
            .lookup_external, .lookup_required => |reference| blk: {
                if (try self.foldedConstant(reference, at, region)) |folded| break :blk folded;
                break :blk self.exprRef(expr_id);
            },
            .match_ => |match_expr| (try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .{ .at = at }, region)).?,
            .block => |block| (try self.blockExpr(block.statements, block.final_expr, .{ .at = at })).?,
            .if_ => |if_expr| (try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .{ .at = at }, region)).?,
            // A transfer delivers nothing here, and a crash has every type.
            .return_, .break_ => self.exprRef(expr_id),
            .crash => |literal| self.bld().crash(at, try self.bld().litStr(self.bodies.stringLiteral(literal))),
            .run_low_level => |run| blk: {
                if (run.op != .crash or run.args.len != 1) break :blk self.exprRef(expr_id);
                break :blk try self.bld().crash(at, try self.exprRef(run.args[0]));
            },
            .lambda, .closure => self.closureAt(expr_id, at),
            .numeral, .str_segment, .str, .binop, .unary_minus, .unary_not, .tuple, .list, .empty_list, .record, .empty_record, .tuple_access, .field_access, .dispatch_call, .type_dispatch_call, .method_eq, .structural_eq, .structural_hash, .dbg, .hosted_lambda, .str_from_quote, .interpolation, .bytes_literal, .expect, .for_, .pending, .code_from_lambda, .runtime_error, .expect_err, .ellipsis, .anno_only => self.exprRef(expr_id),
        };
    }

    fn exprRefs(self: *Reifier, ids: []const CheckedExprId) Error![]Ref {
        const refs = try self.gpa.alloc(Ref, ids.len);
        errdefer self.gpa.free(refs);
        for (ids, refs) |id, *ref| ref.* = try self.exprRef(id);
        return refs;
    }

    /// The value one expression computes, built in the region being built.
    ///
    /// `as` is the type a nominal hands down to the expression that builds
    /// its backing, the nominal's unfolded backing, where the expression's
    /// own checked type is the nominal itself.
    fn exprAs(self: *Reifier, expr_id: CheckedExprId, as: ?TyId) Error!Ref {
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        const b = self.bld();
        // What this expression builds comes from it (N10); what its parts
        // build comes from them.
        var here = [1]reify.provenance.OriginId{try self.walk.originAt(self.artifact, region)};
        const outer = b.origins;
        b.origins = &here;
        defer b.origins = outer;
        return switch (expr_data.data) {
            .numeral => |data| try self.numeralExpr(data, expr_data.ty, region),
            .str_segment => |literal| try b.litStr(self.bodies.stringLiteral(literal)),
            .str => |segments| try self.interpolatedExpr(segments),
            .lookup_local => |lookup| try self.lookupRef(lookup.pattern, lookup.resolved, expr_data.ty, expr_id, null, region),
            .match_ => |match_expr| (try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .value, region)).?,
            .block => |block| (try self.blockExpr(block.statements, block.final_expr, .value)).?,
            .if_ => |if_expr| (try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .value, region)).?,
            .binop => |binop| try self.binopExpr(binop.op, binop.lhs, binop.rhs, expr_data.ty, region),
            .unary_minus => |operand| blk: {
                const value = try self.exprRef(operand);
                const owner = self.primitiveOwner(self.bodies.expr(operand).ty) orelse
                    break :blk self.rejectError(.unsupported_expression, region, "a negation of this type");
                break :blk try b.primOf(try b.namedPrim(owner, "negate"), &.{value}, try self.tyOf(expr_data.ty, region));
            },
            .unary_not => |operand| try b.call(.bool_, .not, &.{try self.exprRef(operand)}),
            .tuple => |items| try self.tupleExpr(items, expr_data.ty, as, region),
            .list => |items| blk: {
                const refs = try self.exprRefs(items);
                defer self.gpa.free(refs);
                break :blk try b.listOf(try self.tyOf(expr_data.ty, region), refs);
            },
            .empty_list => try b.listOf(try self.tyOf(expr_data.ty, region), &.{}),
            .record => |record| try self.recordExpr(record.fields, record.ext, record.unsets, expr_data.ty, as, region),
            .empty_record => try self.recordExpr(&.{}, null, &.{}, expr_data.ty, as, region),
            .tuple_access => |access| try b.index(try self.readable(try self.exprRef(access.tuple)), access.elem_index),
            .field_access => |access| try self.fieldAccessExpr(access.receiver, access.segments, expr_data.ty, region),
            // A crash the compiler wrote carries its message as a literal.
            .crash => |literal| try b.crash(try self.tyOf(expr_data.ty, region), try b.litStr(self.bodies.stringLiteral(literal))),
            // `Type.method(args)` resolves to the same plan a value dispatch
            // leaves behind, and the plan names the dispatcher, so the two
            // are built through one arm.
            .dispatch_call, .type_dispatch_call => |plan_id| try self.dispatchExpr(plan_id, expr_data.ty, region),
            // A hand-written `is_eq` is an ordinary method call; `!=` rides on
            // the plan's result mode, which `dispatchExpr` reads.
            .method_eq => |plan_id| try self.dispatchExpr(plan_id, expr_data.ty, region),
            .structural_eq => |eq| blk: {
                const operand_ty = self.bodies.expr(eq.lhs).ty;
                const lhs = try self.exprRef(eq.lhs);
                const rhs = try self.exprRef(eq.rhs);
                const compare = try self.eqOver(lhs, rhs, operand_ty, region);
                // N1k: `!=` is `Bool.not` of the equality.
                break :blk if (eq.negated) try b.call(.bool_, .not, &.{compare}) else compare;
            },
            .structural_hash => |hash| try self.hashExpr(hash.value, hash.hasher, expr_data.ty, region),
            .dbg => self.rejectError(.effect, region, "dbg"),
            .hosted_lambda => self.rejectError(.effect, region, "a hosted function"),
            .nominal => |nominal| try self.nominalExpr(nominal.backing_expr, expr_data.ty, as, region),
            // The value at the wider tag union this node's type is.
            .row_coerce => |coerce| try self.exprAt(coerce.value, as orelse try self.tyOf(expr_data.ty, region)),
            .tag => |tag_expr| try self.tagExpr(tag_expr.name, tag_expr.args, expr_data.ty, as, region),
            .zero_argument_tag => |tag_expr| try self.tagExpr(tag_expr.name, &.{}, expr_data.ty, as, region),
            .call => |call| try self.callExpr(call.func, call.args, expr_data.ty, null, region),
            .lambda, .closure => try self.closureAt(expr_id, null),
            // A name of another module holds no binding in the scope, so it is
            // the value it was fixed to, or the definition it names.
            .lookup_external, .lookup_required => |reference| blk: {
                if (try self.foldedConstant(reference, null, region)) |folded| break :blk folded;
                if (reference) |resolved| {
                    if (self.functionOf(expr_data.ty) != null) break :blk try self.functionValue(resolved, null, expr_data.ty, region);
                }
                break :blk self.rejectError(.unsupported_expression, region, exprFormName(expr_data.data));
            },
            // A quoted literal is its text where its type is `Str`, and
            // otherwise the `from_quote` call the checker wrote: the
            // conversion may parse or validate.
            .str_from_quote => |quote| blk: {
                const ty = try self.tyOf(expr_data.ty, region);
                if (self.rt().get(ty) == .str) break :blk try b.litStr(self.bodies.stringLiteral(quote.literal));
                break :blk try self.dispatchExpr(quote.plan, expr_data.ty, region);
            },
            // An interpolated literal of the author's own type is the
            // `from_interpolation` call the checker wrote: the method decides
            // what the pieces become.
            .interpolation => |interpolation| try self.interpolationExpr(interpolation, expr_data.ty, region),
            // An embedded file, which is the one expression a `List(U8)`
            // literal is written as.
            .bytes_literal => |literal| try b.litBytes(try self.tyOf(expr_data.ty, region), self.bodies.stringLiteral(literal)),
            // N1j: an assertion for Roc's own test run has no meaning in a
            // target, so it is the `{}` it evaluates to.
            .expect => try b.record(try self.tyOf(expr_data.ty, region), &.{}),
            .return_ => |returned| try self.returnTransfer(returned.expr),
            .break_ => try self.breakTransfer(region),
            .for_ => |loop| blk: {
                try self.forLoop(loop.pattern, loop.expr, loop.body, loop.plan, loop.mutations, region);
                break :blk try b.record(try self.tyOf(expr_data.ty, region), &.{});
            },
            .pending,
            .code_from_lambda,
            .runtime_error,
            .expect_err,
            .ellipsis,
            .anno_only,
            => self.rejectError(.unsupported_expression, region, exprFormName(expr_data.data)),
            // A written `crash` arrives as an intrinsic rather than as the
            // checked `.crash` a compiler-written one does, and it is the one
            // intrinsic the normal form has a node for.
            .run_low_level => |run| blk: {
                if (run.op != .crash or run.args.len != 1) {
                    break :blk self.rejectError(.unsupported_expression, region, exprFormName(expr_data.data));
                }
                const message = try self.exprRef(run.args[0]);
                break :blk try b.crash(try self.tyOf(expr_data.ty, region), message);
            },
        };
    }

    /// An expression whose value nothing reads: a statement.
    fn discard(self: *Reifier, expr_id: CheckedExprId) Error!void {
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        switch (expr_data.data) {
            .if_ => |if_expr| _ = try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .none, region),
            .match_ => |match_expr| _ = try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .none, region),
            .block => |block| _ = try self.blockExpr(block.statements, block.final_expr, .none),
            .for_ => |loop| try self.forLoop(loop.pattern, loop.expr, loop.body, loop.plan, loop.mutations, region),
            .expect => {},
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
            .ellipsis,
            .anno_only,
            .break_,
            .return_,
            .hosted_lambda,
            .run_low_level,
            => _ = try self.exprRef(expr_id),
        }
    }

    /// An interpolated literal of the author's own type, which the language
    /// converts in two stages (langref "Static dispatch"). The first stage is
    /// `from_interpolation` over the literal's segments, which are literals,
    /// so the walk runs it by its definition where the literal stands: a
    /// builtin it wraps, such as `Str.from_interpolation`, is walked too, and
    /// so is every lambda it applies, until the lambda it hands back in its
    /// `Ok` is a closure of a row. The second stage is that closure applied
    /// to the list of the interpolated values, a `Call` of the row over its
    /// captures and the list. The `Err` of the first stage is the crash of a
    /// rejected literal, as the `Err` of a `from_numeral` is
    /// (`convertedWith`), and the rule N13w drops the branches that reach it.
    /// A conversion of another package is one `Prim` over the segments and
    /// the values.
    fn interpolationExpr(self: *Reifier, interpolation: checked.CheckedInterpolation, checked_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const id = interpolation.plan orelse return self.rejectError(.unresolved_reference, region, "this literal");
        const plan = self.plans.plans[@backingInt(id)];
        const b = self.bld();
        const types = self.rt();
        const out_ty = try self.tyOf(checked_ty, region);
        const item_ty = switch (types.get(try self.tyOf(interpolation.assembler_ty, region))) {
            .func => |assembler| switch (types.get(types.tySlice(assembler.params)[0])) {
                .list => |item| item,
                .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => invariant("an assembler takes a list"),
            },
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive => invariant("an interpolation's assembler is a function"),
        };
        // Every segment is kept, the empty ones too: the assembler reads them by position.
        const segments = try self.exprRefs(interpolation.segments);
        defer self.gpa.free(segments);
        const values = try self.exprRefs(interpolation.values);
        defer self.gpa.free(values);
        const segment_list = try b.listOf(try types.listTy(try types.strTy()), segments);
        const value_list = try b.listOf(try types.listTy(item_ty), values);
        switch (try self.dispatchTarget(DispatchSpec.ofPlan(plan), region)) {
            .definition => |target| {
                self.walk.stage_one += 1;
                defer self.walk.stage_one -= 1;
                const converted = try self.inlineCall(target, &.{segment_list}, null, region);
                return self.convertedWith(converted, value_list, checked_ty, region);
            },
            .foreign => |name| return b.primOf(try b.namedPrim(name.owner, name.method), &.{ segment_list, value_list }, out_ty),
            .provided, .none => return self.rejectError(.unresolved_reference, region, "a method this literal names no target for"),
        }
    }

    /// A numeric literal: one `Lit` of its type (N1i), or, for a literal of
    /// the author's own type, the `from_numeral` call the checker wrote.
    fn numeralExpr(self: *Reifier, data: checked.CheckedNumeralData, checked_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const primitive = self.primitiveOf(checked_ty) orelse
            return self.dispatchExpr(data.plan, checked_ty, region);
        return self.numeralLit(data.literal, primitive, try self.tyOf(checked_ty, region), region);
    }

    /// The `Lit` a numeric literal is at the builtin type `ty`.
    fn numeralLit(
        self: *Reifier,
        literal: ModuleEnv.NumeralLiteral,
        primitive: checked.CheckedBuiltinNominal,
        ty: TyId,
        region: base.Region,
    ) Error!Ref {
        const exact = self.env.exactNumeral(literal);
        const b = self.bld();
        return switch (primitive) {
            .f32 => b.litFloatBits(ty, @as(u32, @bitCast(try numeral.floatBits(f32, self.gpa, exact)))),
            .f64 => b.litFloatBits(ty, @bitCast(try numeral.floatBits(f64, self.gpa, exact))),
            .dec => b.litDec(try numeral.decBits(self.gpa, exact) orelse
                return self.rejectError(.unsupported_expression, region, "this numeric literal")),
            .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => b.litInt(ty, switch (numeral.intBits(exact, intTarget(primitive).?) orelse
                return self.rejectError(.unsupported_expression, region, "this numeric literal")) {
                .i128 => |signed| signed,
                .u128 => |magnitude| @as(i128, @bitCast(magnitude)),
            }),
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
            => self.rejectError(.unsupported_type, region, "a numeric literal of this type"),
        };
    }

    /// A string literal of several segments: the `Str.concat` chain it is
    /// (N1e). An empty segment joins nothing to anything and is left out.
    fn interpolatedExpr(self: *Reifier, segments: []const CheckedExprId) Error!Ref {
        var parts = std.ArrayList(Ref).empty;
        defer parts.deinit(self.gpa);
        for (segments) |segment| {
            if (self.isEmptySegment(segment)) continue;
            try parts.append(self.gpa, try self.exprRef(segment));
        }
        const b = self.bld();
        return switch (parts.items.len) {
            0 => b.litStr(""),
            1 => parts.items[0],
            else => b.call(.str, .concat, parts.items),
        };
    }

    /// Whether one segment of a string literal is text the author left empty.
    fn isEmptySegment(self: *Reifier, expr_id: CheckedExprId) bool {
        const data = self.bodies.expr(expr_id).data;
        if (data != .str_segment) return false;
        return self.bodies.stringLiteral(data.str_segment).len == 0;
    }

    /// A binary operator the checker left as one: `and` and `or` as n-ary
    /// `And` and `Or` (N1c), and an arithmetic or comparison operator as the
    /// builtin of its operands' type.
    fn binopExpr(
        self: *Reifier,
        op: CIR.Expr.Binop.Op,
        lhs_id: CheckedExprId,
        rhs_id: CheckedExprId,
        result_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        switch (op) {
            .@"and", .@"or" => return self.connective(op == .@"and", lhs_id, rhs_id),
            .add, .sub, .mul, .div, .div_trunc, .rem, .lt, .le, .gt, .ge, .eq, .ne => {},
            .range_exclusive, .range_inclusive => return self.rejectError(.unsupported_expression, region, "a range outside a `for`"),
        }
        const owner = self.primitiveOwner(self.bodies.expr(lhs_id).ty) orelse
            return self.rejectError(.unsupported_expression, region, "this operator");
        const lhs = try self.exprRef(lhs_id);
        const rhs = try self.exprRef(rhs_id);
        const b = self.bld();
        const method = binopMethod(op);
        if (op == .ne) {
            const eq = try b.primOf(try b.namedPrim(owner, "is_eq"), &.{ lhs, rhs }, try self.rt().boolTy());
            return b.call(.bool_, .not, &.{eq});
        }
        return b.primOf(try b.namedPrim(owner, method), &.{ lhs, rhs }, try self.tyOf(result_ty, region));
    }

    /// `a and b` or `a or b`: `b` is an operand region, run only where `a`
    /// did not decide the result. An operand that can exit the row is a
    /// `Switch` on `a` instead, the connective's meaning written out, because
    /// an operand region delivers a value on every path.
    fn connective(self: *Reifier, is_and: bool, lhs_id: CheckedExprId, rhs_id: CheckedExprId) Error!Ref {
        const b = self.bld();
        const first = try self.exprRef(lhs_id);
        if (self.transfers(rhs_id)) {
            var plan = try self.branchPlan(&.{rhs_id}, .value, try self.rt().boolTy());
            defer plan.deinit(self.gpa);
            var br = Branching.begin(self, &plan);
            const scope_base = self.scope.items.len;
            // `a and b` is `b` where `a` holds and `False` where it does not;
            // `a or b` is `True` where `a` holds and `b` where it does not.
            var arms: [2]RegionId = undefined;
            for (&arms, 0..) |*arm, key| {
                arm.* = try br.openArm(first, @intCast(key));
                const decided = (key == 0) == is_and;
                if (decided) {
                    try br.leaf(try b.litBool(!is_and), scope_base);
                } else try br.leaf(some(self.exprRef(rhs_id)), scope_base);
            }
            return (try br.finish(first, &arms, &.{})).?;
        }
        const operand = try b.openOperand(&.{first}, if (is_and) .and_ else .or_);
        const second = self.exprRef(rhs_id) catch |err| switch (err) {
            error.Diverged => invariant("an operand the scan found no exit in diverged"),
            error.Rejected, error.OutOfMemory => |e| return e,
        };
        try b.close(.{ .value = &.{second} });
        return if (is_and) b.andOf(first, &.{operand}) else b.orOf(first, &.{operand});
    }

    /// A tuple, in the nominal's backing where one hands `as` down.
    fn tupleExpr(self: *Reifier, items: []const CheckedExprId, checked_ty: CheckedTypeId, as: ?TyId, region: base.Region) Error!Ref {
        const refs = try self.exprRefs(items);
        defer self.gpa.free(refs);
        const target = as orelse try self.tyOf(checked_ty, region);
        const b = self.bld();
        return switch (self.rt().get(target)) {
            .nominal => b.wrap(target, try b.tuple(try self.rt().unfold(target), refs)),
            .tuple => b.tuple(target, refs),
            .bool_, .str, .int, .float, .dec, .record, .tag_union, .list, .func, .opaque_, .recursive => self.rejectError(.unsupported_type, region, "a tuple of this type"),
        };
    }

    /// A record literal, in the type's field order, and a record update as
    /// the full record it builds (N1g).
    ///
    /// A field the literal unsets (`b: _`), or leaves out where the type marks
    /// it optional, is a member the `Record` node does not set
    /// (`ir.RecordForm`). An update carries a field it did not write from its
    /// subject, and a subject's optional field may be absent, so the update
    /// is a switch on whether the subject holds it: the arm where it does
    /// sets it, and the arm where it does not leaves it unset.
    fn recordExpr(
        self: *Reifier,
        fields: []const checked.CheckedRecordExprField,
        ext: ?CheckedExprId,
        unsets: []const canonical.RecordFieldLabelId,
        checked_ty: CheckedTypeId,
        as: ?TyId,
        region: base.Region,
    ) Error!Ref {
        const target = as orelse try self.tyOf(checked_ty, region);
        const types = self.rt();
        const shape = switch (types.get(target)) {
            .nominal => try types.unfold(target),
            .record => target,
            .bool_, .str, .int, .float, .dec, .tuple, .tag_union, .list, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a record of this type"),
        };
        // The subject of an update is written first, then the fields, and
        // they are built in that order.
        const subject = if (ext) |subject_id| try self.readable(try self.exprRef(subject_id)) else null;
        const members_len = types.memberSlice(types.get(shape).record).len;
        const values = try self.gpa.alloc(?Ref, members_len);
        defer self.gpa.free(values);
        @memset(values, null);
        const unset = try self.gpa.alloc(bool, members_len);
        defer self.gpa.free(unset);
        @memset(unset, false);
        for (fields) |field| {
            const value = try self.exprRef(field.value);
            const index = self.memberIndex(shape, self.names.recordFieldLabelText(field.label)) orelse
                return self.rejectError(.unsupported_type, region, "a field the record's type does not have");
            values[index] = value;
        }
        for (unsets) |label| {
            const index = self.memberIndex(shape, self.names.recordFieldLabelText(label)) orelse
                return self.rejectError(.unsupported_type, region, "a field the record's type does not have");
            std.debug.assert(types.memberSlice(types.get(shape).record)[index].optional);
            unset[index] = true;
        }
        var carried = std.ArrayList(Carry).empty;
        defer carried.deinit(self.gpa);
        if (subject) |from| {
            try self.carryMembers(from, shape, values, unset, &carried, region);
        } else for (values, unset, 0..) |value, is_unset, index| {
            if (value != null or is_unset) continue;
            // No subject: the checker accepts a literal that leaves out only
            // an optional field, which is then unset.
            if (!types.memberSlice(types.get(shape).record)[index].optional) {
                return self.rejectError(.unsupported_expression, region, "a record literal that leaves out a field");
            }
        }
        return self.recordSetting(target, shape, values, carried.items, subject, region);
    }

    /// Take each member of `shape` that `values` leaves null, and `unset` does
    /// not unset, from the record `from`. A field `from` always holds is a
    /// read. An optional one is a read where `from` holds it and is left
    /// unset where it does not, which only `from`'s value says, so it goes
    /// into `carried`.
    fn carryMembers(
        self: *Reifier,
        from: Ref,
        shape: TyId,
        values: []?Ref,
        unset: []const bool,
        carried: *std.ArrayList(Carry),
        region: base.Region,
    ) Error!void {
        const b = self.bld();
        const types = self.rt();
        for (values, unset, 0..) |*value, is_unset, index| {
            if (value.* != null or is_unset) continue;
            const member = types.memberSlice(types.get(shape).record)[index];
            const at = try self.fieldIndex(from, types.nameText(member.name), region);
            const held = types.memberSlice(types.get(self.irs().refTy(b.row, from)).record)[at];
            if (member.optional and held.optional) {
                try carried.append(self.gpa, .{ .member = @intCast(index), .at = at });
            } else value.* = try b.field(from, at);
        }
    }

    /// A member an update takes from its subject if the subject holds it.
    const Carry = struct {
        /// The member's position in the record type.
        member: u32,
        /// Its position in the subject's record type.
        at: u32,
    };

    /// The record `shape` setting the members `values` holds, in `target`,
    /// and, for each member of `carried`, the member too in the arm where
    /// the subject holds it. The members `values` leaves null and `carried`
    /// does not name are unset.
    fn recordSetting(
        self: *Reifier,
        target: TyId,
        shape: TyId,
        values: []const ?Ref,
        carried: []const Carry,
        subject: ?Ref,
        region: base.Region,
    ) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        if (carried.len == 0) {
            const set = try self.gpa.alloc(u32, values.len);
            defer self.gpa.free(set);
            const refs = try self.gpa.alloc(Ref, values.len);
            defer self.gpa.free(refs);
            var count: usize = 0;
            for (values, 0..) |value, index| {
                const v = value orelse continue;
                set[count] = @intCast(index);
                refs[count] = v;
                count += 1;
            }
            const record = try b.recordSetting(shape, set[0..count], refs[0..count]);
            return if (shape == target) record else b.wrap(target, record);
        }
        const from = subject.?;
        const first = carried[0];
        const ok_ty = types.tySlice(types.memberSlice(types.get(self.irs().refTy(b.row, from)).record)[first.at].tys)[0];
        const found = try self.readable(try b.optField(from, first.at, try self.missingFieldTry(ok_ty)));
        const union_ty = self.irs().refTy(b.row, found);
        const ok = try types.name("Ok");
        const names = try self.memberNames(union_ty, region);
        defer self.gpa.free(names);
        const arms = try self.gpa.alloc(RegionId, names.len);
        defer self.gpa.free(arms);
        const own = try self.gpa.dupe(?Ref, values);
        defer self.gpa.free(own);
        for (arms, names) |*arm, name| {
            arm.* = try b.openTagArm(found, name);
            own[first.member] = if (name == ok) try b.payload(found, ok, 0) else null;
            const built = try self.recordSetting(target, shape, own, carried[1..], subject, region);
            try b.close(.{ .value = &.{built} });
        }
        return b.switchOn(found, arms, &.{}, &.{target}, &.{});
    }

    /// `Try(ok, [MissingField])`, the type the checker gives a `.?` read
    /// (`mkTryContent` over `makeFieldMissingTag`, `src/check/Check.zig`).
    fn missingFieldTry(self: *Reifier, ok_ty: TyId) Error!TyId {
        return self.tryOver(ok_ty, "MissingField");
    }

    /// `Try(ok, [err])`, for the one payload-free tag `err`.
    fn tryOver(self: *Reifier, ok_ty: TyId, err: []const u8) Error!TyId {
        const types = self.rt();
        const err_ty = try types.tagUnionTy(&.{.{ .name = err, .payload = &.{} }});
        const backing = try types.tagUnionTy(&.{
            .{ .name = "Err", .payload = &.{err_ty} },
            .{ .name = "Ok", .payload = &.{ok_ty} },
        });
        return types.nominalTy(try_type_name, backing);
    }

    /// The name the type table gives the builtin `Try`: the registry entry
    /// the canonicalizer interns the builtin's qualified name from, so it is
    /// the text `typeNameText` answers for the checker's own `Try`
    /// (`src/canonicalize/CIR.zig` (`builtin_type_specs`)). The `.?` assert
    /// in `optionalPath` holds the two together: the type built here must be
    /// the type the checker gave the path.
    const try_type_name = CIR.builtinTypeSpec("try_type").qualified_name;

    /// A field access path, one read per segment. A segment written `.?`
    /// reads a field the type marks optional and hands back the
    /// `Try(a, [MissingField])` the value sits in. The checker gives the
    /// whole path one flat `Try` of the last field's type, and the first
    /// optional segment found missing is the `Err` of all of it, so an
    /// optional segment before the last is a switch on its own `Try`: the
    /// `Err` arm is the path's `Err`, and the `Ok` arm reads the rest.
    fn fieldAccessExpr(
        self: *Reifier,
        receiver_id: CheckedExprId,
        segments: []const checked.CheckedFieldAccessSegment,
        path_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        const b = self.bld();
        const receiver = try self.exprRef(receiver_id);
        const optional = for (segments) |segment| {
            if (segment.mode == .optional) break true;
        } else false;
        if (!optional) {
            var value = receiver;
            for (segments) |segment| {
                const record = try self.readable(value);
                value = try b.field(record, try self.fieldIndex(record, self.names.recordFieldLabelText(segment.field_name), segment.source_region));
            }
            return value;
        }
        return self.optionalPath(receiver, segments, try self.tyOf(path_ty, region), region);
    }

    /// The rest of a path that holds an optional segment, read from `value`,
    /// as the `Try` of type `path`.
    fn optionalPath(self: *Reifier, value: Ref, segments: []const checked.CheckedFieldAccessSegment, path: TyId, region: base.Region) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        var current = value;
        for (segments, 1..) |segment, walked| {
            const record = try self.readable(current);
            const index = try self.fieldIndex(record, self.names.recordFieldLabelText(segment.field_name), segment.source_region);
            if (segment.mode == .required) {
                current = try b.field(record, index);
                continue;
            }
            const field_ty = types.tySlice(types.memberSlice(types.get(self.irs().refTy(b.row, record)).record)[index].tys)[0];
            const found = try b.optField(record, index, try self.missingFieldTry(field_ty));
            if (walked == segments.len) {
                // The last segment's `Try` is the path's own.
                std.debug.assert(self.irs().refTy(b.row, found) == path);
                return found;
            }
            const union_value = try self.readable(found);
            const ok = try types.name("Ok");
            const names = try self.memberNames(self.irs().refTy(b.row, union_value), region);
            defer self.gpa.free(names);
            const arms = try self.gpa.alloc(RegionId, names.len);
            defer self.gpa.free(arms);
            for (arms, names) |*arm, name| {
                arm.* = try b.openTagArm(union_value, name);
                const delivered = if (name == ok)
                    try self.optionalPath(try b.payload(union_value, ok, 0), segments[walked..], path, region)
                else
                    try self.pathTry(path, "Err", null, region);
                try b.close(.{ .value = &.{delivered} });
            }
            return b.switchOn(union_value, arms, &.{}, &.{path}, &.{});
        }
        return self.pathTry(path, "Ok", current, region);
    }

    /// The path's `Try` holding the `Ok` value, or the `Err(MissingField)`.
    fn pathTry(self: *Reifier, path: TyId, tag_text: []const u8, ok_value: ?Ref, region: base.Region) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        const unfolded = try types.unfold(path);
        const name = try self.tagName(unfolded, tag_text, region);
        if (ok_value) |value| return b.wrap(path, try b.tag(unfolded, name, &.{value}));
        const missing_ty = types.tySlice(types.memberSlice(types.get(unfolded).tag_union)[types.memberIndex(unfolded, name).?].tys)[0];
        const missing = try b.tag(missing_ty, try self.tagName(missing_ty, "MissingField", region), &.{});
        return b.wrap(path, try b.tag(unfolded, name, &.{missing}));
    }

    /// A nominal's value: its backing, built at the unfolded backing type,
    /// wrapped in the nominal. `Bool` is no nominal in the normal form, so
    /// its tags are built as the literals they are.
    fn nominalExpr(self: *Reifier, backing_id: CheckedExprId, checked_ty: CheckedTypeId, as: ?TyId, region: base.Region) Error!Ref {
        const target = as orelse try self.tyOf(checked_ty, region);
        return switch (self.rt().get(target)) {
            .nominal => self.bld().wrap(target, try self.exprAs(backing_id, try self.rt().unfold(target))),
            .bool_ => self.exprAs(backing_id, target),
            .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .recursive => self.exprAs(backing_id, target),
            .opaque_ => self.rejectError(.unsupported_type, region, "a value of an opaque type"),
        };
    }

    /// A tag: a `Bool` literal, or a variant of a tag union, wrapped in the
    /// nominal its type is where it is one.
    fn tagExpr(
        self: *Reifier,
        name: canonical.TagLabelId,
        args: []const CheckedExprId,
        checked_ty: CheckedTypeId,
        as: ?TyId,
        region: base.Region,
    ) Error!Ref {
        const target = as orelse try self.tyOf(checked_ty, region);
        const b = self.bld();
        switch (self.rt().get(target)) {
            .bool_ => {
                const flag = self.bool_tags.value(name) orelse return self.rejectError(.unsupported_expression, region, "a tag");
                return b.litBool(flag);
            },
            .nominal => return b.wrap(target, try self.variantIn(try self.rt().unfold(target), name, args, region)),
            .tag_union => return self.variantIn(target, name, args, region),
            .str, .int, .float, .dec, .record, .tuple, .list, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a tag of this type"),
        }
    }

    /// A variant of `union_ty`, each payload built at the type the union
    /// gives it.
    fn variantIn(self: *Reifier, union_ty: TyId, name: canonical.TagLabelId, args: []const CheckedExprId, region: base.Region) Error!Ref {
        const tag_name = try self.tagName(union_ty, self.names.tagLabelText(name), region);
        const payloads = try self.gpa.alloc(Ref, args.len);
        defer self.gpa.free(payloads);
        for (args, payloads, 0..) |arg, *payload, k| {
            // Read the member again each time: a payload's walk interns types.
            const types = self.rt();
            const index = types.memberIndex(union_ty, tag_name).?;
            const component_tys = types.tySlice(types.memberSlice(types.get(union_ty).tag_union)[index].tys);
            if (component_tys.len != args.len) return self.rejectError(.unsupported_type, region, "a tag whose payload count differs from its union's");
            payload.* = try self.exprAt(arg, component_tys[k]);
        }
        return self.bld().tag(union_ty, tag_name, payloads);
    }

    /// The value a name stands for: its binding in scope, the statement
    /// that binds it replayed, or the constant or top-level function it
    /// resolves to.
    ///
    /// `use_ty` is the type the lookup has, which a function a block
    /// generalized is instantiated at. A constant the name folds to is built
    /// at `at` where it is given (`exprAt`).
    fn lookupRef(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        resolved: ?checked.ResolvedValueRefId,
        use_ty: CheckedTypeId,
        use_expr: ?CheckedExprId,
        at: ?TyId,
        region: base.Region,
    ) Error!Ref {
        const binder = self.bodies.patternBinderForCheckedPattern(pattern_id) orelse
            return self.rejectError(.unresolved_reference, region, "this reference");
        const binding = self.lookupBinding(binder) orelse try self.replayBinding(binder) orelse
            return self.unboundRef(binder, resolved, use_ty, at, region);
        return self.bindingValue(binding, use_ty, use_expr, region);
    }

    /// A reference no scope binds: a constant, or a top-level function used
    /// as a value.
    fn unboundRef(
        self: *Reifier,
        binder: PatternBinderId,
        resolved: ?checked.ResolvedValueRefId,
        use_ty: CheckedTypeId,
        at: ?TyId,
        region: base.Region,
    ) Error!Ref {
        if (try self.foldedConstant(resolved, at, region)) |folded| return folded;
        if (resolved) |id| {
            if (self.functionOf(use_ty) != null) return self.functionValue(id, binder, use_ty, region);
        }
        if (self.walk.inputs) |*inputs| {
            if (inputs.reader == self) return self.inputSlot(inputs, binder, region);
        }
        return self.rejectError(.capture, region, self.binderName(binder));
    }

    /// The input slot of a run-time name the walk cannot replay (N18a), at a
    /// site whose translator returns a `Code.Bound`
    /// (`roc-reify-proposal.md` section 10.1). The program supplies the
    /// value at the call, so the name has to be the value the description
    /// reads there: a `var` can be written again before the call, and a row
    /// other than the root has no call of its own to supply it at.
    fn inputSlot(self: *Reifier, inputs: *Walk.Inputs, binder: PatternBinderId, region: base.Region) Error!Ref {
        const record = self.bodies.patternBinder(binder);
        if (record.reassignable) return self.rejectError(.input_not_bound, region, "a `var`, whose value at the call is not always the value the description reads");
        if (self.walk.rows.items.len != 1) return self.rejectError(.input_not_bound, region, "a value that a function inside the description reads from around the lambda");
        const pattern = self.bodies.pattern(record.pattern);
        const ty = try self.tyOf(pattern.ty, pattern.source_region);
        const leaf: u32 = for (inputs.leaves.items, 0..) |known, i| {
            if (known == binder) break @intCast(i);
        } else blk: {
            try inputs.leaves.append(self.gpa, binder);
            break :blk @intCast(inputs.leaves.items.len - 1);
        };
        return self.bld().input(ty, leaf);
    }

    fn bindingValue(self: *Reifier, binding: Binding, use_ty: CheckedTypeId, use_expr: ?CheckedExprId, region: base.Region) Error!Ref {
        return switch (binding.kind) {
            .value => |value| value,
            // The value the template call fixed, walked where it is read.
            .constant => |constant| constant.reader.exprRef(constant.expr),
            .function => |value_id| blk: {
                // A lambda the block bound is a closure of its row. A function
                // a call handed back is that call, built where it is read.
                if (self.lambdaOf(value_id) == null) break :blk try self.exprRef(value_id);
                const target = (try self.liftedTarget(binding, use_ty, use_expr, region)).definition;
                break :blk try self.closureOf(target, try self.tyOf(use_ty, region));
            },
            .callee => |index| try self.closureOf(try self.boundTarget(self.bound[index].target), try self.tyOf(use_ty, region)),
        };
    }

    /// A top-level function used as a value: a closure of its row, which
    /// captures nothing.
    fn functionValue(
        self: *Reifier,
        resolved: checked.ResolvedValueRefId,
        written_binder: ?PatternBinderId,
        use_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        // A top-level value that computes a function is the definition it was
        // written as, built where the name stands, as a constant is.
        if (try self.computedFunction(resolved, region)) |computed| switch (computed) {
            .written => |written| return try self.foldedBody(written.reader, written.body, null) orelse
                self.rejectError(.unsupported_expression, region, "a top-level constant that computes a function and reads itself"),
            .foreign => return self.rejectError(.unsupported_expression, region, "a function of the compiler or of another package used as a value"),
        };
        return switch (try self.resolvedTarget(resolved, written_binder, region)) {
            .definition => |target| self.closureOf(target, try self.tyOf(use_ty, region)),
            .provided, .foreign => self.rejectError(.unsupported_expression, region, "a function of the compiler or of another package used as a value"),
            .value => self.rejectError(.unsupported_expression, region, "a function value that names no definition"),
        };
    }

    /// Where a name bound to a compile-time constant leads: the reader that
    /// holds the value's body, and the body.
    ///
    /// The checker resolves such a name to a `ConstRef`, and the template that
    /// ref names holds the checked body the value was written as. A name the
    /// running program computes resolves to something else and answers null.
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

    /// The value a name holds, built where the name stands.
    ///
    /// The fold is by definition: the body the constant was written as is
    /// walked where the name stands, so a translator never learns that a name
    /// stood there, and there is no capture to lower. A constant written as
    /// data folds to that data. A computed one, `limit = 7.0 * 2.0`, folds to
    /// the computation, which reads only names the compiler fixes, so it needs
    /// no value the compiler evaluates after the description is built.
    /// Where the use reads a wider tag union than the value's own (`at`),
    /// the body is built at it, as it would be if written at the use.
    fn foldedConstant(
        self: *Reifier,
        resolved: ?checked.ResolvedValueRefId,
        at: ?TyId,
        region: base.Region,
    ) Error!?Ref {
        const definition = try self.constantDefinition(resolved) orelse return null;
        const reader = definition.reader;
        // A computation of another package is a body of that package, which
        // the walk does not read, as it does not read that package's
        // functions (N8h).
        if (!reader.folding.contains(definition.body) and !samePackage(self.env, reader.env) and !try self.nameHoldsConstant(resolved)) {
            return self.rejectError(.unsupported_expression, region, "a computed constant of another package");
        }
        return self.foldedBody(reader, definition.body, at);
    }

    /// The definition `body` of `reader`'s module, built where a name stands.
    /// Null for a definition that reads itself, which is refused on the repeat
    /// rather than followed forever.
    fn foldedBody(self: *Reifier, reader: *Reifier, body: CheckedExprId, at: ?TyId) Error!?Ref {
        _ = self;
        if (reader.folding.contains(body)) return null;
        try reader.folding.put(reader.gpa, body, {});
        defer _ = reader.folding.remove(body);
        return if (at) |ty| try reader.exprAt(body, ty) else try reader.exprRef(body);
    }

    /// A top-level value that computes a function, `doubler = make(2.0)`.
    ///
    /// The compiler evaluates such a value after the description is built, so
    /// the closure it holds is not known to the walk. What the walk knows is
    /// the definition, and it reads that where the name stands, the way it
    /// reads a computed constant. The definition names the lambda's row and
    /// every capture, so no value the compiler evaluates is needed.
    const ComputedFunction = union(enum) {
        /// The definition, and the reader of the module that wrote it.
        written: struct { reader: *Reifier, body: CheckedExprId },
        /// A value of another package: its definition is a body of that
        /// package, which the walk does not read (N8h), so a call on it is a
        /// `Prim` named by the module and the value.
        foreign: ForeignName,
    };

    /// Where a name that is a top-level value computing a function leads, or
    /// null for any other name, an exact alias of a function included: its
    /// lookup names the procedure it forwards to.
    fn computedFunction(self: *Reifier, resolved: checked.ResolvedValueRefId, region: base.Region) Error!?ComputedFunction {
        const use = switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| use,
            .local_proc,
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .selected_hoisted_const,
            .top_level_const,
            .imported_const,
            .hosted_proc,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            => return null,
        };
        switch (use.binding) {
            .top_level => |top_level| {
                if (!std.meta.eql(top_level.artifact.bytes, self.artifact.bytes)) return null;
                const template_id = switch (self.procedure_bindings.get(top_level.binding).body) {
                    .callable_eval_template => |id| id,
                    .direct_template, .checked_error => return null,
                };
                const template = self.callable_eval_templates.templates[@backingInt(template_id)];
                if (template.forwarded_lookup != null) return null;
                return .{ .written = .{ .reader = self, .body = template.body } };
            },
            .imported => |imported| {
                const away = self.walk.foreign.findExportedComputed(imported.artifact, imported.def) orelse return null;
                const reader = try self.walk.reader(away.module);
                if (samePackage(self.env, reader.env)) return .{ .written = .{ .reader = reader, .body = away.body } };
                if (reader.env.module_role == .builtin) {
                    return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides");
                }
                const binder = reader.bodies.patternBinderForCheckedPattern(imported.pattern) orelse
                    return reader.rejectError(.unresolved_reference, region, "this call");
                return .{ .foreign = .{ .owner = reader.env.module_name, .method = reader.binderName(binder) } };
            },
            .hosted, .platform_required => return null,
        }
    }

    // Control //

    /// End the region being built in `end`, and say so. At the row body the
    /// row ends; anywhere else the region closes, and whoever opened it
    /// catches the `error.Diverged`.
    fn terminate(self: *Reifier, end: Builder.EndSpec) Error!noreturn {
        const b = self.bld();
        if (b.atRowBody()) try b.endRow(end) else try b.close(end);
        return error.Diverged;
    }

    /// `return e`: the row's value, from wherever it stands.
    fn returnTransfer(self: *Reifier, value_id: CheckedExprId) Error!noreturn {
        const value = try self.exprRef(value_id);
        try self.terminate(.{ .return_ = value });
    }

    /// `break`: the loop ends with its slots as they stand.
    fn breakTransfer(self: *Reifier, region: base.Region) Error!noreturn {
        const loop = self.loop orelse return self.rejectError(.unsupported_expression, region, "a break outside a loop");
        const slots = try self.slotValues(loop, if (loop.iterator) Ref.regionParam(loop.body, loop.slot_base) else null, region);
        defer self.gpa.free(slots);
        try self.terminate(.{ .break_ = slots });
    }

    /// The values a loop's slots hold here: the iterator, where the loop has
    /// one, then each carried `var` at the version in scope.
    fn slotValues(self: *Reifier, loop: Loop, iterator: ?Ref, region: base.Region) Error![]Ref {
        const values = try self.gpa.alloc(Ref, loop.carried.len + @intFromBool(iterator != null));
        errdefer self.gpa.free(values);
        var next: usize = 0;
        if (iterator) |it| {
            values[0] = it;
            next = 1;
        }
        for (loop.carried) |binder| {
            values[next] = try self.carriedValue(binder, region);
            next += 1;
        }
        return values;
    }

    fn carriedValue(self: *Reifier, binder: PatternBinderId, region: base.Region) Error!Ref {
        const binding = self.lookupBinding(binder) orelse
            return self.rejectError(.capture, region, self.binderName(binder));
        return switch (binding.kind) {
            .value => |value| value,
            .constant, .function, .callee => self.rejectError(.unsupported_expression, region, "a var that holds a function"),
        };
    }

    /// What a syntactic pass over a construct finds: whether it can leave
    /// the row or the loop around it, and which `var`s it writes. Neither
    /// looks into a lambda, which is a row of its own, or into an `expect`,
    /// which the walk passes over.
    const Scan = struct {
        r: *Reifier,
        /// How many loops inside the construct the pass is in; a `break`
        /// inside one leaves that loop and not the construct.
        loops: u32 = 0,
        transfers: bool = false,
        /// Each `var` an assignment writes, beside the binder the assignment
        /// wrote, which a later read may name instead.
        assigned: std.ArrayList(Assigned) = .empty,

        const Assigned = struct { binder: PatternBinderId, written: ?PatternBinderId };

        fn deinit(s: *Scan) void {
            s.assigned.deinit(s.r.gpa);
        }

        fn scanExprs(s: *Scan, ids: []const CheckedExprId) Allocator.Error!void {
            for (ids) |id| try s.scanExpr(id);
        }

        fn scanExpr(s: *Scan, id: CheckedExprId) Allocator.Error!void {
            const bodies = s.r.bodies;
            switch (bodies.expr(id).data) {
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
                .empty_record,
                .zero_argument_tag,
                .runtime_error,
                .crash,
                .ellipsis,
                .anno_only,
                .hosted_lambda,
                .closure,
                .lambda,
                .expect,
                => {},
                .str, .list, .tuple => |items| try s.scanExprs(items),
                .match_ => |m| {
                    try s.scanExpr(m.cond);
                    for (m.branches) |branch| {
                        if (branch.guard) |guard| try s.scanExpr(guard);
                        try s.scanExpr(branch.value);
                    }
                },
                .if_ => |i| {
                    for (i.branches) |branch| {
                        try s.scanExpr(branch.cond);
                        try s.scanExpr(branch.body);
                    }
                    try s.scanExpr(i.final_else);
                },
                .call => |c| {
                    try s.scanExpr(c.func);
                    try s.scanExprs(c.args);
                },
                .record => |rec| {
                    if (rec.ext) |ext| try s.scanExpr(ext);
                    for (rec.fields) |field| try s.scanExpr(field.value);
                },
                .block => |block| {
                    for (block.statements) |statement| try s.scanStatement(statement);
                    try s.scanExpr(block.final_expr);
                },
                .tag => |t| try s.scanExprs(t.args),
                .nominal => |n| try s.scanExpr(n.backing_expr),
                .row_coerce => |coerce| try s.scanExpr(coerce.value),
                .binop => |op| {
                    try s.scanExpr(op.lhs);
                    try s.scanExpr(op.rhs);
                },
                .unary_minus, .unary_not, .dbg => |operand| try s.scanExpr(operand),
                .field_access => |access| try s.scanExpr(access.receiver),
                .tuple_access => |access| try s.scanExpr(access.tuple),
                .dispatch_call, .method_eq, .type_dispatch_call => |plan_id| if (plan_id) |plan| try s.scanPlan(plan),
                .interpolation => |interpolation| {
                    try s.scanExprs(interpolation.segments);
                    try s.scanExprs(interpolation.values);
                },
                .structural_eq => |eq| {
                    try s.scanExpr(eq.lhs);
                    try s.scanExpr(eq.rhs);
                },
                .structural_hash => |hash| {
                    try s.scanExpr(hash.value);
                    try s.scanExpr(hash.hasher);
                },
                .expect_err => |e| try s.scanExpr(e.expr),
                .break_ => if (s.loops == 0) {
                    s.transfers = true;
                },
                .return_ => |returned| {
                    s.transfers = true;
                    try s.scanExpr(returned.expr);
                },
                .for_ => |loop| {
                    try s.scanExpr(loop.expr);
                    s.loops += 1;
                    defer s.loops -= 1;
                    try s.scanExpr(loop.body);
                },
                .run_low_level => |run| try s.scanExprs(run.args),
            }
        }

        fn scanPlan(s: *Scan, plan_id: static_dispatch.StaticDispatchPlanId) Allocator.Error!void {
            const p = s.r.plans.plans[@backingInt(plan_id)];
            for (p.argsSlice(s.r.plans)) |operand| switch (operand) {
                .checked_expr, .generated_interpolation_segments => |child| try s.scanExpr(child),
                .generated_numeral, .generated_quote => {},
            };
        }

        fn scanStatement(s: *Scan, id: CheckedStatementId) Allocator.Error!void {
            switch (s.r.bodies.statement(id).data) {
                .decl => |decl| try s.scanExpr(decl.expr),
                .var_ => |decl| try s.scanExpr(decl.expr),
                .reassign => |assignment| {
                    try s.scanExpr(assignment.expr);
                    const written = s.r.bodies.patternBinderForCheckedPattern(assignment.pattern);
                    for (assignment.reassigned_binders) |binder| try s.assigned.append(s.r.gpa, .{ .binder = binder, .written = written });
                },
                .dbg, .expr => |e| try s.scanExpr(e),
                .for_ => |loop| {
                    try s.scanExpr(loop.expr);
                    s.loops += 1;
                    defer s.loops -= 1;
                    try s.scanExpr(loop.body);
                },
                .while_, .infinite_loop, .breakable_loop => |loop| {
                    s.loops += 1;
                    defer s.loops -= 1;
                    try s.scanExpr(loop.cond);
                    try s.scanExpr(loop.body);
                },
                .break_ => if (s.loops == 0) {
                    s.transfers = true;
                },
                .return_ => |returned| {
                    s.transfers = true;
                    try s.scanExpr(returned.expr);
                },
                // A promoted function's body is its own procedure, which
                // runs nothing here.
                .promoted_proc,
                .pending,
                .var_uninitialized,
                .crash,
                .expect,
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
    };

    /// Whether an expression can leave the row, or the loop around it.
    fn transfers(self: *Reifier, expr_id: CheckedExprId) bool {
        var s: Scan = .{ .r = self };
        defer s.deinit();
        s.scanExpr(expr_id) catch |err| switch (err) {
            // The pass only allocates for assignments, which this caller
            // does not read, so it answers what it saw before running out.
            error.OutOfMemory => return true,
        };
        return s.transfers;
    }

    /// The `var`s a construct writes that the scope holds as values, which
    /// the construct carries out, and the other binders each is read under.
    const Carried = struct {
        binders: std.ArrayList(PatternBinderId) = .empty,
        aliases: std.ArrayList(Alias) = .empty,

        const Alias = struct { binder: PatternBinderId, index: u32 };

        fn deinit(c: *Carried, gpa: Allocator) void {
            c.binders.deinit(gpa);
            c.aliases.deinit(gpa);
        }

        /// Bind every carried `var`, under each of its names, to `values`.
        fn rebind(c: *const Carried, r: *Reifier, values: []const Ref) Allocator.Error!void {
            for (c.binders.items, values) |binder, value| try r.bindValue(binder, value);
            for (c.aliases.items) |alias| try r.bindValue(alias.binder, values[alias.index]);
        }
    };

    fn carriedOf(self: *Reifier, assigned: []const Scan.Assigned, into: *Carried) Allocator.Error!void {
        for (assigned) |a| {
            const binding = self.lookupBinding(a.binder) orelse continue;
            if (binding.kind != .value) continue;
            const index = positionOf(PatternBinderId, into.binders.items, a.binder) orelse blk: {
                try into.binders.append(self.gpa, a.binder);
                break :blk into.binders.items.len - 1;
            };
            if (a.written) |written| {
                if (written == a.binder) continue;
                const seen = for (into.aliases.items) |alias| {
                    if (alias.binder == written) break true;
                } else false;
                if (!seen) try into.aliases.append(self.gpa, .{ .binder = written, .index = @intCast(index) });
            }
        }
    }

    /// What a branching construct delivers: its value, where one is read,
    /// then each carried `var`; and whether it can exit, which makes it an
    /// exiting switch whose continuation is one join (N11f).
    const BranchPlan = struct {
        exiting: bool,
        /// How each arm's code delivers the value.
        want: Want,
        value_ty: ?TyId,
        carried: Carried = .{},
        /// The output types: the value's, then each carried `var`'s.
        tys: std.ArrayList(TyId) = .empty,

        fn deinit(p: *BranchPlan, gpa: Allocator) void {
            p.carried.deinit(gpa);
            p.tys.deinit(gpa);
        }
    };

    /// A plan whose value, if `want` reads one, has type `value_ty`.
    fn branchPlan(self: *Reifier, roots: []const CheckedExprId, want: Want, value_ty: ?TyId) Error!BranchPlan {
        std.debug.assert((want == .none) == (value_ty == null));
        var s: Scan = .{ .r = self };
        defer s.deinit();
        for (roots) |root| try s.scanExpr(root);
        var plan: BranchPlan = .{ .exiting = s.transfers, .want = want, .value_ty = value_ty };
        errdefer plan.deinit(self.gpa);
        try self.carriedOf(s.assigned.items, &plan.carried);
        if (value_ty) |ty| try plan.tys.append(self.gpa, ty);
        for (plan.carried.binders.items) |binder| {
            const value = self.lookupBinding(binder).?.kind.value;
            try plan.tys.append(self.gpa, self.irs().refTy(self.bld().row, value));
        }
        return plan;
    }

    /// One branching construct being built: its arms, which may nest
    /// switches of their own, all deliver the plan's outputs, by `Value` in
    /// a value switch and by `Jump` to one join in an exiting one.
    const Branching = struct {
        r: *Reifier,
        plan: *const BranchPlan,
        /// Reserved at the first arm, in the region the outermost switch
        /// stands in, for an exiting construct.
        join: RegionId = RegionId.none,
        /// Whether some arm jumps to the join, so code follows the switch.
        continued: bool = false,

        fn begin(r: *Reifier, plan: *const BranchPlan) Branching {
            return .{ .r = r, .plan = plan };
        }

        fn openArm(br: *Branching, scrutinee: Ref, key: u32) Error!RegionId {
            try br.reserve();
            return br.r.bld().openArm(scrutinee, key);
        }

        fn openTagArm(br: *Branching, scrutinee: Ref, name: NameId) Error!RegionId {
            try br.reserve();
            return br.r.bld().openTagArm(scrutinee, name);
        }

        fn openLitArm(br: *Branching, scrutinee: Ref, keys: []const u32, arm: u32) Error!RegionId {
            try br.reserve();
            return br.r.bld().openLitArm(scrutinee, keys, arm);
        }

        fn reserve(br: *Branching) Error!void {
            if (!br.plan.exiting or br.join != RegionId.none) return;
            br.join = try br.r.bld().reserveJoin(br.plan.tys.items);
        }

        /// Close the arm being built with what it delivers: `value`, the
        /// walk of its code, which may have ended the arm itself.
        fn leaf(br: *Branching, value: Error!?Ref, scope_base: usize) Error!void {
            const r = br.r;
            defer r.scope.shrinkRetainingCapacity(scope_base);
            const delivered = value catch |err| switch (err) {
                error.Diverged => return,
                error.Rejected, error.OutOfMemory => |e| return e,
            };
            const outs = try br.outputs(delivered);
            defer r.gpa.free(outs);
            if (br.plan.exiting) {
                br.continued = true;
                try r.bld().close(.{ .jump = .{ .join = br.join, .args = outs } });
            } else try r.bld().close(.{ .value = outs });
        }

        fn outputs(br: *Branching, value: ?Ref) Error![]Ref {
            const r = br.r;
            const outs = try r.gpa.alloc(Ref, br.plan.tys.items.len);
            errdefer r.gpa.free(outs);
            var next: usize = 0;
            if (br.plan.value_ty != null) {
                outs[0] = value.?;
                next = 1;
            }
            for (br.plan.carried.binders.items) |binder| {
                outs[next] = r.lookupBinding(binder).?.kind.value;
                next += 1;
            }
            return outs;
        }

        /// Close the arm being built with a switch over `arms`, nested in it.
        fn inner(br: *Branching, scrutinee: Ref, arms: []const RegionId, keys: []const u32) Error!void {
            const b = br.r.bld();
            if (br.plan.exiting) {
                const sw = try b.exitingSwitch(scrutinee, arms, &.{}, keys);
                try b.close(.{ .branch = sw });
                return;
            }
            const v = try b.switchOn(scrutinee, arms, &.{}, br.plan.tys.items, keys);
            const outs = try br.switchOutputs(v);
            defer br.r.gpa.free(outs);
            try b.close(.{ .value = outs });
        }

        /// End the construct with its outermost switch over `arms`, and hand
        /// back its value, with each carried `var` bound to what it left.
        fn finish(br: *Branching, scrutinee: Ref, arms: []const RegionId, keys: []const u32) Error!?Ref {
            const r = br.r;
            const b = r.bld();
            if (br.plan.exiting) {
                if (!br.continued) {
                    const sw = try b.exitingSwitch(scrutinee, arms, &.{}, keys);
                    try r.terminate(.{ .branch = sw });
                }
                const sw = try b.exitingSwitch(scrutinee, arms, &.{br.join}, keys);
                try b.continueIn(sw, br.join);
                const outs = try r.gpa.alloc(Ref, br.plan.tys.items.len);
                defer r.gpa.free(outs);
                for (outs, 0..) |*out, k| out.* = Ref.regionParam(br.join, @intCast(k));
                return br.settle(outs);
            }
            const v = try b.switchOn(scrutinee, arms, &.{}, br.plan.tys.items, keys);
            const outs = try br.switchOutputs(v);
            defer r.gpa.free(outs);
            return br.settle(outs);
        }

        fn settle(br: *Branching, outs: []const Ref) Error!?Ref {
            const has_value = br.plan.value_ty != null;
            try br.plan.carried.rebind(br.r, outs[@intFromBool(has_value)..]);
            return if (has_value) outs[0] else null;
        }

        fn switchOutputs(br: *Branching, v: Ref) Error![]Ref {
            const n = br.plan.tys.items.len;
            const outs = try br.r.gpa.alloc(Ref, n);
            if (n == 1) {
                outs[0] = v;
            } else for (outs, 0..) |*out, k| out.* = Ref.node(v.nodeId(), @intCast(k));
            return outs;
        }
    };

    /// What a construct's code delivers: nothing, its value, or its value
    /// at a type its position fixes, where that differs from the value's own
    /// checked type (see `exprAt`).
    const Want = union(enum) { none, value, at: TyId };

    /// The type of the value `want` reads from a construct of `checked_ty`.
    fn valueTy(self: *Reifier, want: Want, checked_ty: CheckedTypeId, region: base.Region) Error!?TyId {
        return switch (want) {
            .none => null,
            .value => try self.tyOf(checked_ty, region),
            .at => |ty| ty,
        };
    }

    /// The walk of an arm's code, delivering its value when one is read.
    fn armCode(self: *Reifier, expr_id: CheckedExprId, want: Want) Error!?Ref {
        switch (want) {
            .none => {
                try self.discard(expr_id);
                return null;
            },
            .value => return try self.exprRef(expr_id),
            .at => |ty| return try self.exprAt(expr_id, ty),
        }
    }

    /// `if`: nested `Bool` switches, arm 0 the `else` and arm 1 the `then`
    /// (N1c), with every carried `var` an output.
    fn ifExpr(
        self: *Reifier,
        branches: []const checked.CheckedIfBranch,
        final_else: CheckedExprId,
        checked_ty: CheckedTypeId,
        want: Want,
        region: base.Region,
    ) Error!?Ref {
        var roots = std.ArrayList(CheckedExprId).empty;
        defer roots.deinit(self.gpa);
        for (branches) |branch| try roots.appendSlice(self.gpa, &.{ branch.cond, branch.body });
        try roots.append(self.gpa, final_else);
        var plan = try self.branchPlan(roots.items, want, try self.valueTy(want, checked_ty, region));
        defer plan.deinit(self.gpa);
        var br = Branching.begin(self, &plan);
        return self.ifLevel(&br, branches, final_else, true);
    }

    fn ifLevel(self: *Reifier, br: *Branching, branches: []const checked.CheckedIfBranch, final_else: CheckedExprId, top: bool) Error!?Ref {
        const b = self.bld();
        if (branches.len == 0) return self.armBody(br, final_else, top);
        const cond = try self.exprRef(branches[0].cond);
        if (b.knownKey(cond)) |key| {
            return if (key == 1) self.armBody(br, branches[0].body, top) else self.ifLevel(br, branches[1..], final_else, top);
        }
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        arms[0] = try br.openArm(cond, 0);
        try closedArm(self.ifLevel(br, branches[1..], final_else, false));
        self.scope.shrinkRetainingCapacity(scope_base);
        arms[1] = try br.openArm(cond, 1);
        try br.leaf(self.armCode(branches[0].body, br.plan.want), scope_base);
        if (top) return br.finish(cond, &arms, &.{});
        try br.inner(cond, &arms, &.{});
        return null;
    }

    /// The code of one arm: at the construct's top, where every test on the
    /// way was decided, it is built in place; inside an arm, it closes it.
    fn armBody(self: *Reifier, br: *Branching, expr_id: CheckedExprId, top: bool) Error!?Ref {
        if (top) return try self.armCode(expr_id, br.plan.want);
        try br.leaf(self.armCode(expr_id, br.plan.want), self.scope.items.len);
        return null;
    }

    /// A value, as the arm result `Branching.leaf` takes.
    fn some(value: Error!Ref) Error!?Ref {
        return try value;
    }

    /// A nested level closed its arm, or the arm ended itself.
    fn closedArm(result: Error!?Ref) Error!void {
        _ = result catch |err| switch (err) {
            error.Diverged => return,
            error.Rejected, error.OutOfMemory => |e| return e,
        };
    }

    // Match //

    /// Where a `match` goes when a test fails: the next alternative of the
    /// branch, then the next branch.
    const MatchAt = struct {
        branches: []const checked.CheckedMatchBranch,
        branch: usize,
        alternative: usize,
    };

    /// One pattern and the value it tests.
    const Test = struct { pattern: CheckedPatternId, value: Ref };

    /// `match`: a first-match cascade of switches (N1c). Each alternative's
    /// pattern is a queue of tests, left to right; a failing test goes on to
    /// the next alternative, and past the last branch to the crash Roc
    /// lowers the case to.
    fn matchExpr(
        self: *Reifier,
        cond_id: CheckedExprId,
        branches: []const checked.CheckedMatchBranch,
        checked_ty: CheckedTypeId,
        want: Want,
        region: base.Region,
    ) Error!?Ref {
        const subject = try self.exprRef(cond_id);
        var roots = std.ArrayList(CheckedExprId).empty;
        defer roots.deinit(self.gpa);
        for (branches) |branch| {
            if (branch.guard) |guard| try roots.append(self.gpa, guard);
            try roots.append(self.gpa, branch.value);
        }
        var plan = try self.branchPlan(roots.items, want, try self.valueTy(want, checked_ty, region));
        defer plan.deinit(self.gpa);
        var br = Branching.begin(self, &plan);
        return self.matchFrom(&br, subject, .{ .branches = branches, .branch = 0, .alternative = 0 }, true, region);
    }

    fn matchFrom(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, top: bool, region: base.Region) Error!?Ref {
        if (at.branch == at.branches.len) return self.noBranch(br, top);
        const branch = at.branches[at.branch];
        const alternative = branch.patternsSlice(self.bodies)[at.alternative];
        var queue = std.ArrayList(Test).empty;
        defer queue.deinit(self.gpa);
        try queue.append(self.gpa, .{ .pattern = alternative.pattern, .value = subject });
        return self.testQueue(br, subject, at, queue.items, top, region);
    }

    /// Where the cascade goes when the alternative `at` fails.
    fn failed(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, top: bool, region: base.Region) Error!?Ref {
        var next = at;
        if (at.alternative + 1 < at.branches[at.branch].patternsSlice(self.bodies).len) {
            next.alternative += 1;
        } else {
            next.branch += 1;
            next.alternative = 0;
        }
        return self.matchFrom(br, subject, next, top, region);
    }

    /// Past the last branch: Roc lowers this case to a runtime error.
    fn noBranch(self: *Reifier, br: *Branching, top: bool) Error!?Ref {
        const b = self.bld();
        const value: ?Ref = if (br.plan.value_ty) |ty| try b.crash(ty, try b.litStr("no branch of this match applies")) else null;
        if (top) return value;
        try br.leaf(value, self.scope.items.len);
        return null;
    }

    /// The alternative `at` matched: bind the names its alternatives share,
    /// test the guard, and deliver the branch's value.
    fn matched(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, top: bool, region: base.Region) Error!?Ref {
        const branch = at.branches[at.branch];
        const alternative = branch.patternsSlice(self.bodies)[at.alternative];
        for (alternative.binderRemapsSlice(self.bodies)) |remap| {
            if (remap.candidate_binder == remap.representative_binder) continue;
            const binding = self.lookupBinding(remap.candidate_binder) orelse
                invariant("a matched alternative left a binder it binds unbound");
            try self.scope.append(self.gpa, .{ .binder = remap.representative_binder, .kind = binding.kind });
        }
        const guard_id = branch.guard orelse return self.armBody(br, branch.value, top);
        const guard = try self.exprRef(guard_id);
        return self.boolTest(br, subject, at, guard, true, .{ .value = branch.value }, top, region);
    }

    /// What follows a test that holds: the rest of the queue, or the
    /// branch's value once the guard held.
    const Then = union(enum) {
        queue: []const Test,
        value: CheckedExprId,
        list: ListReads,
        str: StrReads,
    };

    /// A `Bool` switch on `flag`: the arm where it is `holds` goes on to
    /// `then`, the other to the next alternative.
    fn boolTest(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, flag: Ref, holds: bool, then: Then, top: bool, region: base.Region) Error!?Ref {
        const pass_key: u32 = @intFromBool(holds);
        if (self.bld().knownKey(flag)) |key| {
            if (key == pass_key) return self.thenOf(br, subject, at, then, top, region);
            return self.failed(br, subject, at, top, region);
        }
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        for (&arms, 0..) |*arm, key| {
            arm.* = try br.openArm(flag, @intCast(key));
            if (key == pass_key) {
                try closedArm(self.thenOf(br, subject, at, then, false, region));
            } else try closedArm(self.failed(br, subject, at, false, region));
            self.scope.shrinkRetainingCapacity(scope_base);
        }
        if (top) return br.finish(flag, &arms, &.{});
        try br.inner(flag, &arms, &.{});
        return null;
    }

    fn thenOf(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, then: Then, top: bool, region: base.Region) Error!?Ref {
        return switch (then) {
            .queue => |queue| self.testQueue(br, subject, at, queue, top, region),
            .value => |value| self.armBody(br, value, top),
            .list => |reads| self.listReads(br, subject, at, reads, top),
            .str => |reads| self.strReads(br, subject, at, reads, top),
        };
    }

    /// The queue with its first test replaced by `parts`.
    fn expanded(self: *Reifier, queue: []const Test, parts: []const Test) Allocator.Error![]Test {
        const out = try self.gpa.alloc(Test, parts.len + queue.len - 1);
        @memcpy(out[0..parts.len], parts);
        @memcpy(out[parts.len..], queue[1..]);
        return out;
    }

    /// Run the tests of `queue` in order.
    fn testQueue(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, queue: []const Test, top: bool, region: base.Region) Error!?Ref {
        if (queue.len == 0) return self.matched(br, subject, at, top, region);
        const b = self.bld();
        const t = queue[0];
        const pattern = self.bodies.pattern(t.pattern);
        switch (pattern.data) {
            .assign => |binder| {
                try self.bindValue(binder, t.value);
                return self.testQueue(br, subject, at, queue[1..], top, region);
            },
            .underscore => return self.testQueue(br, subject, at, queue[1..], top, region),
            .as => |renamed| {
                try self.bindValue(renamed.binder, t.value);
                const rest = try self.expanded(queue, &.{.{ .pattern = renamed.pattern, .value = t.value }});
                defer self.gpa.free(rest);
                return self.testQueue(br, subject, at, rest, top, region);
            },
            .nominal => |nominal| {
                const rest = try self.expanded(queue, &.{.{ .pattern = nominal.backing_pattern, .value = try self.unwrapOnce(t.value) }});
                defer self.gpa.free(rest);
                return self.testQueue(br, subject, at, rest, top, region);
            },
            .tuple => |items| {
                const tuple = try self.readable(t.value);
                const parts = try self.gpa.alloc(Test, items.len);
                defer self.gpa.free(parts);
                for (items, parts, 0..) |item, *part, k| part.* = .{ .pattern = item, .value = try b.index(tuple, @intCast(k)) };
                const rest = try self.expanded(queue, parts);
                defer self.gpa.free(rest);
                return self.testQueue(br, subject, at, rest, top, region);
            },
            .record_destructure => |destructs| {
                const record = try self.readable(t.value);
                var parts = std.ArrayList(Test).empty;
                defer parts.deinit(self.gpa);
                for (destructs) |destruct| {
                    const inner = switch (destruct.kind) {
                        .required, .sub_pattern => |inner| inner,
                        .rest => |inner| {
                            if (self.bodies.pattern(inner).data == .underscore) continue;
                            // The name binds a record of the fields the pattern
                            // does not name, which is the record those reads
                            // build.
                            const rest_ty = try self.tyOf(self.bodies.pattern(inner).ty, pattern.source_region);
                            try parts.append(self.gpa, .{ .pattern = inner, .value = try self.restRecord(record, rest_ty, pattern.source_region) });
                            continue;
                        },
                    };
                    const index = try self.fieldIndex(record, self.names.recordFieldLabelText(destruct.label), pattern.source_region);
                    try parts.append(self.gpa, .{ .pattern = inner, .value = try b.field(record, index) });
                }
                const rest = try self.expanded(queue, parts.items);
                defer self.gpa.free(rest);
                return self.testQueue(br, subject, at, rest, top, region);
            },
            .applied_tag => |applied| return self.tagTest(br, subject, at, queue, applied.name, applied.args, top, region),
            .numeral_literal => |literal| {
                if (literal.guard) |guard| return self.guardedTest(br, subject, at, queue, guard, top, region);
                return self.numeralTest(br, subject, at, queue, literal.literal, top, region);
            },
            .str_literal => |literal| {
                if (literal.guard) |guard| return self.guardedTest(br, subject, at, queue, guard, top, region);
                const text = try b.litStr(self.bodies.stringLiteral(literal.literal));
                const eq = try b.call(.str, .is_eq, &.{ try self.readable(t.value), text });
                return self.boolTest(br, subject, at, eq, true, .{ .queue = queue[1..] }, top, region);
            },
            .list => |list| return self.listTest(br, subject, at, queue, list.patterns, list.rest, top, region),
            .str_interpolation => |str| return self.strTest(br, subject, at, queue, str.prefix, str.steps, str.end, top, region),
            .pending, .runtime_error => return self.rejectError(.unsupported_expression, pattern.source_region, patternFormName(pattern.data)),
        }
    }

    /// The record of type `rest_ty` that `..rest` binds: each of its fields
    /// read from `record`.
    fn restRecord(self: *Reifier, record: Ref, rest_ty: TyId, region: base.Region) Error!Ref {
        const types = self.rt();
        const members_len = switch (types.get(rest_ty)) {
            .record => |span| span.len,
            .bool_, .str, .int, .float, .dec, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a record pattern rest of this type"),
        };
        const values = try self.gpa.alloc(?Ref, members_len);
        defer self.gpa.free(values);
        @memset(values, null);
        const unset = try self.gpa.alloc(bool, members_len);
        defer self.gpa.free(unset);
        @memset(unset, false);
        var carried = std.ArrayList(Carry).empty;
        defer carried.deinit(self.gpa);
        try self.carryMembers(record, rest_ty, values, unset, &carried, region);
        return self.recordSetting(rest_ty, rest_ty, values, carried.items, record, region);
    }

    /// A literal pattern of the author's own type: the checker wrote the
    /// equality, which reads the pattern's own binder.
    fn guardedTest(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, queue: []const Test, guard_id: CheckedExprId, top: bool, region: base.Region) Error!?Ref {
        const t = queue[0];
        const binder = self.bodies.patternBinderForCheckedPattern(t.pattern) orelse
            invariant("a guarded literal pattern has no binder for its guard to read");
        try self.bindValue(binder, t.value);
        const eq = try self.exprRef(guard_id);
        return self.boolTest(br, subject, at, eq, true, .{ .queue = queue[1..] }, top, region);
    }

    /// A tag pattern: a `Bool` literal as a `Bool` switch, and a variant as
    /// a switch on the union, where the matching arm tests the payloads.
    fn tagTest(
        self: *Reifier,
        br: *Branching,
        subject: Ref,
        at: MatchAt,
        queue: []const Test,
        name: canonical.TagLabelId,
        args: []const CheckedPatternId,
        top: bool,
        region: base.Region,
    ) Error!?Ref {
        const b = self.bld();
        const value = try self.readable(queue[0].value);
        const ty = self.irs().refTy(b.row, value);
        switch (self.rt().get(ty)) {
            .bool_ => {
                const flag = self.bool_tags.value(name) orelse return self.rejectError(.unsupported_expression, region, "a tag pattern on a Bool");
                return self.boolTest(br, subject, at, value, flag, .{ .queue = queue[1..] }, top, region);
            },
            .tag_union => {
                // The scrutinee has every tag the match lists: a call carries
                // the type its site reads it at, so a helper that closes a row
                // is read at the wider union the match lists.
                const tag_name = self.rt().findName(self.names.tagLabelText(name)) orelse
                    invariant("a pattern names a tag no type of the site has");
                if (!b.tagLive(value, tag_name)) invariant("a pattern names a tag the scrutinee cannot hold");
                const members = try self.memberNames(ty, region);
                defer self.gpa.free(members);
                const parts = try self.gpa.alloc(Test, args.len);
                defer self.gpa.free(parts);
                if (members.len == 1) {
                    for (args, parts, 0..) |arg, *part, k| part.* = .{ .pattern = arg, .value = try b.payload(value, tag_name, @intCast(k)) };
                    const rest = try self.expanded(queue, parts);
                    defer self.gpa.free(rest);
                    return self.testQueue(br, subject, at, rest, top, region);
                }
                if (b.knownKey(value)) |key| {
                    if (key != tag_name.index()) return self.failed(br, subject, at, top, region);
                    for (args, parts, 0..) |arg, *part, k| part.* = .{ .pattern = arg, .value = try b.payload(value, tag_name, @intCast(k)) };
                    const rest = try self.expanded(queue, parts);
                    defer self.gpa.free(rest);
                    return self.testQueue(br, subject, at, rest, top, region);
                }
                const arms = try self.gpa.alloc(RegionId, members.len);
                defer self.gpa.free(arms);
                const scope_base = self.scope.items.len;
                for (arms, members) |*arm, member| {
                    arm.* = try br.openTagArm(value, member);
                    if (member == tag_name) {
                        for (args, parts, 0..) |arg, *part, k| part.* = .{ .pattern = arg, .value = try b.payload(value, tag_name, @intCast(k)) };
                        const rest = try self.expanded(queue, parts);
                        defer self.gpa.free(rest);
                        try closedArm(self.testQueue(br, subject, at, rest, false, region));
                    } else try closedArm(self.failed(br, subject, at, false, region));
                    self.scope.shrinkRetainingCapacity(scope_base);
                }
                if (top) return br.finish(value, arms, &.{});
                try br.inner(value, arms, &.{});
                return null;
            },
            .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a tag pattern on this type"),
        }
    }

    /// A numeric literal pattern of a builtin type: an integer as a literal
    /// switch keyed by it, a float or `Dec` by its `is_eq`.
    fn numeralTest(
        self: *Reifier,
        br: *Branching,
        subject: Ref,
        at: MatchAt,
        queue: []const Test,
        literal: ModuleEnv.NumeralLiteral,
        top: bool,
        region: base.Region,
    ) Error!?Ref {
        const b = self.bld();
        const value = try self.readable(queue[0].value);
        const ty = self.irs().refTy(b.row, value);
        const primitive = self.primitiveOfTy(ty) orelse
            return self.rejectError(.unsupported_type, region, "a numeric pattern of this type");
        const lit = try self.numeralLit(literal, primitive, ty, region);
        switch (self.rt().get(ty)) {
            .int => {},
            .float, .dec => {
                const owner = primitiveOwnerText(primitive).?;
                const eq = try b.primOf(try b.namedPrim(owner, "is_eq"), &.{ value, lit }, try self.rt().boolTy());
                return self.boolTest(br, subject, at, eq, true, .{ .queue = queue[1..] }, top, region);
            },
            .bool_, .str, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => return self.rejectError(.unsupported_type, region, "a numeric pattern of this type"),
        }
        const lit_id = LitId.of(self.irs().node(lit.nodeId()).payload);
        if (b.litFact(value, lit_id)) |holds| {
            if (holds) return self.testQueue(br, subject, at, queue[1..], top, region);
            return self.failed(br, subject, at, top, region);
        }
        const keys = [_]u32{lit_id.index()};
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        arms[0] = try br.openLitArm(value, &keys, 0);
        try closedArm(self.testQueue(br, subject, at, queue[1..], false, region));
        self.scope.shrinkRetainingCapacity(scope_base);
        arms[1] = try br.openLitArm(value, &keys, 1);
        try closedArm(self.failed(br, subject, at, false, region));
        self.scope.shrinkRetainingCapacity(scope_base);
        if (top) return br.finish(value, &arms, &keys);
        try br.inner(value, &arms, &keys);
        return null;
    }

    /// A list pattern: its length tested, exactly by a literal switch or at
    /// least by `is_gte`, then each element read by `Elem` under that test,
    /// and a named rest bound to the list with both ends dropped.
    fn listTest(
        self: *Reifier,
        br: *Branching,
        subject: Ref,
        at: MatchAt,
        queue: []const Test,
        items: []const CheckedPatternId,
        rest: ?checked.CheckedListRestPattern,
        top: bool,
        region: base.Region,
    ) Error!?Ref {
        const b = self.bld();
        const list = try self.readable(queue[0].value);
        const u64_ty = try self.rt().intTy(.u64);
        const len = try b.call(.list, .len, &.{list});
        const count = try b.litInt(u64_ty, @intCast(items.len));
        const reads: Then = .{ .list = .{ .list = list, .len = len, .items = items, .rest = rest, .queue = queue, .region = region } };
        if (rest != null) {
            const long_enough = try b.call(.u64, .is_gte, &.{ len, count });
            return self.boolTest(br, subject, at, long_enough, true, reads, top, region);
        }
        const lit_id = LitId.of(self.irs().node(count.nodeId()).payload);
        if (b.litFact(len, lit_id)) |holds| {
            if (holds) return self.thenOf(br, subject, at, reads, top, region);
            return self.failed(br, subject, at, top, region);
        }
        const keys = [_]u32{lit_id.index()};
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        arms[0] = try br.openLitArm(len, &keys, 0);
        try closedArm(self.thenOf(br, subject, at, reads, false, region));
        self.scope.shrinkRetainingCapacity(scope_base);
        arms[1] = try br.openLitArm(len, &keys, 1);
        try closedArm(self.failed(br, subject, at, false, region));
        self.scope.shrinkRetainingCapacity(scope_base);
        if (top) return br.finish(len, &arms, &keys);
        try br.inner(len, &arms, &keys);
        return null;
    }

    /// What a list pattern reads once its length test held: each element,
    /// and the rest.
    const ListReads = struct {
        list: Ref,
        len: Ref,
        items: []const CheckedPatternId,
        rest: ?checked.CheckedListRestPattern,
        /// The queue whose first test is this list pattern.
        queue: []const Test,
        region: base.Region,
    };

    /// Read a list pattern's elements where its length test holds, and run
    /// the tests on them.
    fn listReads(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: ListReads, top: bool) Error!?Ref {
        const b = self.bld();
        const u64_ty = try self.rt().intTy(.u64);
        const items = reads.items;
        const named_rest: ?CheckedPatternId = if (reads.rest) |r| r.pattern else null;
        const parts = try self.gpa.alloc(Test, items.len + @intFromBool(named_rest != null));
        defer self.gpa.free(parts);
        const before: usize = if (reads.rest) |r| r.index else items.len;
        for (items, 0..) |item, k| {
            const index = if (k < before)
                try b.litInt(u64_ty, @intCast(k))
            else
                try b.call(.u64, .minus, &.{ reads.len, try b.litInt(u64_ty, @intCast(items.len - k)) });
            parts[k] = .{ .pattern = item, .value = try b.elem(reads.list, index, try self.tyOf(self.bodies.pattern(item).ty, reads.region)) };
        }
        if (named_rest) |rest_pattern| {
            const list_ty = self.irs().refTy(b.row, reads.list);
            const dropped = try b.primOf(try b.namedPrim("List", "drop_first"), &.{ reads.list, try b.litInt(u64_ty, @intCast(before)) }, list_ty);
            const middle = try b.primOf(try b.namedPrim("List", "drop_last"), &.{ dropped, try b.litInt(u64_ty, @intCast(items.len - before)) }, list_ty);
            parts[items.len] = .{ .pattern = rest_pattern, .value = middle };
        }
        const tail = try self.expanded(reads.queue, parts);
        defer self.gpa.free(tail);
        return self.testQueue(br, subject, at, tail, top, reads.region);
    }

    /// A string interpolation pattern, as the decisions and reads Roc makes
    /// for it (`LIR.strMatchStep`): the text starts with the prefix; each
    /// step but a final tail capture splits the text left at the first place
    /// its delimiter appears, capturing what comes before it; an exact end
    /// leaves no text. A test that fails goes on to the next alternative.
    fn strTest(
        self: *Reifier,
        br: *Branching,
        subject: Ref,
        at: MatchAt,
        queue: []const Test,
        prefix_id: checked.CheckedStringLiteralId,
        steps: []const checked.CheckedStrPatternStep,
        end: checked.CheckedStrPatternEnd,
        top: bool,
        region: base.Region,
    ) Error!?Ref {
        const b = self.bld();
        const text = try self.readable(queue[0].value);
        const prefix = self.bodies.stringLiteral(prefix_id);
        var captures = std.ArrayList(Test).empty;
        defer captures.deinit(self.gpa);
        const reads: StrReads = .{ .text = text, .prefix = prefix, .steps = steps, .end = end, .queue = queue, .captures = &captures, .region = region };
        if (prefix.len == 0) return self.strReads(br, subject, at, reads, top);
        const starts = try b.primOf(try b.namedPrim("Str", "starts_with"), &.{ text, try b.litStr(prefix) }, try self.rt().boolTy());
        return self.boolTest(br, subject, at, starts, true, .{ .str = reads }, top, region);
    }

    /// What a string pattern reads once its prefix matched.
    const StrReads = struct {
        text: Ref,
        prefix: []const u8,
        steps: []const checked.CheckedStrPatternStep,
        end: checked.CheckedStrPatternEnd,
        /// The queue whose first test is this string pattern.
        queue: []const Test,
        /// The captures read so far, as the tests of their patterns.
        captures: *std.ArrayList(Test),
        region: base.Region,
    };

    /// Drop the prefix, and go on to the steps.
    fn strReads(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: StrReads, top: bool) Error!?Ref {
        const b = self.bld();
        const str_ty = try self.rt().strTy();
        const rest = if (reads.prefix.len == 0)
            reads.text
        else
            try b.primOf(try b.namedPrim("Str", "drop_prefix"), &.{ reads.text, try b.litStr(reads.prefix) }, str_ty);
        return self.strSteps(br, subject, at, reads, rest, reads.steps, top);
    }

    /// The steps of a string pattern from the text `rest` that is left.
    fn strSteps(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: StrReads, rest: Ref, steps: []const checked.CheckedStrPatternStep, top: bool) Error!?Ref {
        const b = self.bld();
        const region = reads.region;
        const captured = reads.captures.items.len;
        defer reads.captures.shrinkRetainingCapacity(captured);
        const step = steps[0];
        const last = steps.len == 1;
        if (last and reads.end == .tail) {
            if (step.capture) |capture| try reads.captures.append(self.gpa, .{ .pattern = capture, .value = rest });
            return self.strDone(br, subject, at, reads, top);
        }
        const str_ty = try self.rt().strTy();
        const pair_ty = try self.rt().recordTy(&.{ .{ .name = "after", .ty = str_ty }, .{ .name = "before", .ty = str_ty } });
        const split_ty = try self.tryOver(pair_ty, "NotFound");
        const split = try b.primOf(try b.namedPrim("Str", "split_first"), &.{ rest, try b.litStr(self.bodies.stringLiteral(step.delimiter)) }, split_ty);
        const found = try self.readable(split);
        const ok = try self.rt().name("Ok");
        const names = try self.memberNames(self.irs().refTy(b.row, found), region);
        defer self.gpa.free(names);
        const arms = try self.gpa.alloc(RegionId, names.len);
        defer self.gpa.free(arms);
        const scope_base = self.scope.items.len;
        for (arms, names) |*arm, name| {
            arm.* = try br.openTagArm(found, name);
            if (name == ok) {
                const pair = try self.readable(try b.payload(found, ok, 0));
                if (step.capture) |capture| {
                    const before = try b.field(pair, try self.fieldIndex(pair, "before", region));
                    try reads.captures.append(self.gpa, .{ .pattern = capture, .value = before });
                }
                const after = try b.field(pair, try self.fieldIndex(pair, "after", region));
                if (last) {
                    // An exact end leaves no text after the last delimiter.
                    const empty = try b.primOf(try b.namedPrim("Str", "is_empty"), &.{after}, try self.rt().boolTy());
                    try closedArm(self.strEnd(br, subject, at, reads, empty, false));
                } else try closedArm(self.strSteps(br, subject, at, reads, after, steps[1..], false));
                reads.captures.shrinkRetainingCapacity(captured);
            } else try closedArm(self.failed(br, subject, at, false, region));
            self.scope.shrinkRetainingCapacity(scope_base);
        }
        if (top) return br.finish(found, arms, &.{});
        try br.inner(found, arms, &.{});
        return null;
    }

    /// The pattern ended where `empty` says no text is left: the tests of
    /// the captures and then of the queue run where it holds.
    fn strEnd(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: StrReads, empty: Ref, top: bool) Error!?Ref {
        const tail = try self.expanded(reads.queue, reads.captures.items);
        defer self.gpa.free(tail);
        return self.boolTest(br, subject, at, empty, true, .{ .queue = tail }, top, reads.region);
    }

    /// The pattern matched whatever text is left: the tests of the captures
    /// and then of the queue.
    fn strDone(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: StrReads, top: bool) Error!?Ref {
        const tail = try self.expanded(reads.queue, reads.captures.items);
        defer self.gpa.free(tail);
        return self.testQueue(br, subject, at, tail, top, reads.region);
    }

    // Blocks //

    /// A block: its statements in order, then its final expression. Each
    /// `var` of the enclosing scope keeps the version the block left it at.
    fn blockExpr(self: *Reifier, statements: []const CheckedStatementId, final_expr: CheckedExprId, want: Want) Error!?Ref {
        const scope_base = self.scope.items.len;
        for (statements) |statement_id| try self.walkStatement(statement_id);
        const value = try self.armCode(final_expr, want);
        try self.leaveScope(scope_base);
        return value;
    }

    fn walkStatement(self: *Reifier, statement_id: CheckedStatementId) Error!void {
        const statement_data = self.bodies.statement(statement_id);
        const region = statement_data.source_region;
        switch (statement_data.data) {
            .decl => |decl| try self.declStatement(decl.pattern, decl.expr),
            // A `var` binds a name the way any other binding does; an
            // assignment after it binds a new version (N3).
            .var_ => |decl| try self.declStatement(decl.pattern, decl.expr),
            .reassign => |assignment| {
                if (assignment.reassigned_binders.len != 1) {
                    return self.rejectError(.unsupported_expression, region, "an assignment that writes more than one name");
                }
                // Walked before the new version is bound: `x = x + 1` reads
                // the version it replaces.
                const value = try self.exprRef(assignment.expr);
                const binder = assignment.reassigned_binders[0];
                try self.bindValue(binder, value);
                // A read after the assignment names whichever of the two
                // binders the checker recorded, so both hold the version.
                if (self.bodies.patternBinderForCheckedPattern(assignment.pattern)) |written| {
                    if (written != binder) try self.bindValue(written, value);
                }
            },
            // A written crash in statement position: the rest of the block
            // is what C2 leaves unconstrained, so the crash is a node of
            // its own.
            .crash => |literal| {
                const b = self.bld();
                _ = try b.crash(try self.rt().recordTy(&.{}), try b.litStr(self.bodies.stringLiteral(literal)));
            },
            .dbg => return self.rejectError(.effect, region, "dbg"),
            .expr => |discarded| try self.discard(discarded),
            // N1j: an assertion for Roc's own test run has no meaning in a
            // target.
            .expect => {},
            .for_ => |loop| try self.forLoop(loop.pattern, loop.expr, loop.body, loop.plan, loop.mutations, region),
            .while_ => |loop| try self.conditionLoop(loop.cond, loop.body, loop.mutations, true, region),
            // `while Bool.True { .. }` reaches the walk as one of these two:
            // the body runs until it breaks or returns.
            .infinite_loop, .breakable_loop => |loop| try self.conditionLoop(loop.cond, loop.body, loop.mutations, false, region),
            .break_ => try self.breakTransfer(region),
            .return_ => |returned| try self.returnTransfer(returned.expr),
            // A promoted local function evaluates nothing where it is
            // written. Every use of its name resolves to its procedure, which
            // the walk reads as a definition of the module.
            .promoted_proc => {},
            // A type-level statement names a type for the checker and leaves
            // no value behind.
            .import_,
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            => {},
            .pending,
            .var_uninitialized,
            .runtime_error,
            => return self.rejectError(.unsupported_expression, region, statementFormName(statement_data.data)),
        }
    }

    /// `pattern = value`. A binding that holds a function is held rather
    /// than built: a call on it names its row, and a read builds a closure
    /// of it.
    fn declStatement(self: *Reifier, pattern_id: CheckedPatternId, value_id: CheckedExprId) Error!void {
        const region = self.bodies.pattern(pattern_id).source_region;
        if (self.functionOf(self.bodies.expr(value_id).ty) != null) {
            return self.bindName(pattern_id, .{ .function = value_id }, region);
        }
        if (self.bodies.pattern(pattern_id).data == .underscore) return self.discard(value_id);
        try self.bindPattern(pattern_id, try self.exprRef(value_id));
    }

    // Loops //

    /// The `var`s a loop carries, by the checker's mutation plan, in the
    /// plan's order, with the other binders a scan of the body finds each
    /// read under.
    fn loopCarried(self: *Reifier, mutations: ?checked.LoopMutationPlanId, roots: []const CheckedExprId, into: *Carried) Error!void {
        const plan_id = mutations orelse return;
        const mutated = self.bodies.loopMutations(plan_id).binders;
        var s: Scan = .{ .r = self };
        defer s.deinit();
        for (roots) |root| try s.scanExpr(root);
        for (self.bodies.patternBinderIdPool()[mutated.start..][0..mutated.len]) |binder| {
            const binding = self.lookupBinding(binder) orelse continue;
            if (binding.kind != .value) continue;
            if (positionOf(PatternBinderId, into.binders.items, binder) != null) continue;
            try into.binders.append(self.gpa, binder);
        }
        for (s.assigned.items) |a| {
            const written = a.written orelse continue;
            if (written == a.binder) continue;
            const index = positionOf(PatternBinderId, into.binders.items, a.binder) orelse continue;
            try into.aliases.append(self.gpa, .{ .binder = written, .index = @intCast(index) });
        }
    }

    /// `for pattern in iterable { body }`: a `ForRange` over a builtin
    /// integer range, a `ForList` over a list, and a `Loop` over the
    /// iterator protocol otherwise (N11a to N11c).
    fn forLoop(
        self: *Reifier,
        pattern_id: CheckedPatternId,
        iterable_id: CheckedExprId,
        body_id: CheckedExprId,
        plan_id: ?static_dispatch.IteratorForPlanId,
        mutations: ?checked.LoopMutationPlanId,
        region: base.Region,
    ) Error!void {
        var carried: Carried = .{};
        defer carried.deinit(self.gpa);
        try self.loopCarried(mutations, &.{body_id}, &carried);
        if (try self.rangeOf(iterable_id)) |range| {
            const start = try self.exprRef(range.start);
            const end = try self.exprRef(range.end);
            return self.countedLoop(.{ .range = .{ .inclusive = range.inclusive, .start = start, .end = end } }, pattern_id, body_id, &carried, region);
        }
        const iterable_ty = self.bodies.expr(iterable_id).ty;
        if (self.primitiveOf(iterable_ty) == .list) {
            const list = try self.exprRef(iterable_id);
            return self.countedLoop(.{ .list = list }, pattern_id, body_id, &carried, region);
        }
        const plan = self.plans.iterator_for_plans[
            @backingInt(plan_id orelse
                return self.rejectError(.unresolved_reference, region, "this for loop"))
        ];
        try self.iteratorLoop(plan, pattern_id, body_id, &carried, region);
    }

    /// The bounds of a range a `for` walks, where the iterable is a range
    /// method of a builtin integer.
    const Range = struct { inclusive: bool, start: CheckedExprId, end: CheckedExprId };

    fn rangeOf(self: *Reifier, iterable_id: CheckedExprId) Error!?Range {
        const data = self.bodies.expr(iterable_id).data;
        if (data != .dispatch_call) return null;
        const plan_id = data.dispatch_call orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const inclusive = self.ranges.inclusiveOf(plan.method) orelse return null;
        const primitive = self.primitiveOf(plan.dispatcher_ty) orelse return null;
        if (intTarget(primitive) == null) return null;
        const operands = plan.argsSlice(self.plans);
        if (operands.len != 2) return null;
        const start = switch (operands[0]) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments => return null,
        };
        const end = switch (operands[1]) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments => return null,
        };
        return .{ .inclusive = inclusive, .start = start, .end = end };
    }

    const Counted = union(enum) {
        range: struct { inclusive: bool, start: Ref, end: Ref },
        list: Ref,
    };

    /// A loop over a range or a list: the body's parameters are the index,
    /// the element for a list, then the slots; its end is `Continue` with
    /// the next slots.
    fn countedLoop(self: *Reifier, counted: Counted, pattern_id: CheckedPatternId, body_id: CheckedExprId, carried: *const Carried, region: base.Region) Error!void {
        const b = self.bld();
        const initial = try self.slotValues(.{ .body = RegionId.none, .slot_base = 0, .iterator = false, .carried = carried.binders.items }, null, region);
        defer self.gpa.free(initial);
        const slot_tys = try self.gpa.alloc(TyId, initial.len);
        defer self.gpa.free(slot_tys);
        for (initial, slot_tys) |value, *ty| ty.* = self.irs().refTy(b.row, value);

        var params = std.ArrayList(TyId).empty;
        defer params.deinit(self.gpa);
        const bounds: [2]Ref = switch (counted) {
            .range => |range| .{ range.start, range.end },
            .list => |list| .{ list, list },
        };
        switch (counted) {
            .range => try params.append(self.gpa, self.irs().refTy(b.row, bounds[0])),
            .list => |list| {
                try params.append(self.gpa, try self.rt().intTy(.u64));
                const list_ty = self.irs().refTy(b.row, list);
                try params.append(self.gpa, switch (self.rt().get(list_ty)) {
                    .list => |elem| elem,
                    .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => invariant("a list loop's list is not a list"),
                });
            },
        }
        const slot_base: u30 = @intCast(params.items.len);
        try params.appendSlice(self.gpa, slot_tys);

        const body = try b.openRegion(.loop_body, params.items);
        switch (counted) {
            .range => {},
            .list => |list| try b.noteListLoop(body, list),
        }
        try self.loopBody(.{ .body = body, .slot_base = slot_base, .iterator = false, .carried = carried.binders.items }, carried, body_id, switch (counted) {
            .range => .{ .item = .{ .pattern = pattern_id, .value = Ref.regionParam(body, 0) } },
            .list => .{ .item = .{ .pattern = pattern_id, .value = Ref.regionParam(body, 1) } },
        }, region);

        var args = std.ArrayList(Ref).empty;
        defer args.deinit(self.gpa);
        const loop = switch (counted) {
            .range => |range| blk: {
                try args.appendSlice(self.gpa, &.{ range.start, range.end });
                try args.appendSlice(self.gpa, initial);
                break :blk try b.forRange(range.inclusive, args.items, body, slot_tys);
            },
            .list => |list| blk: {
                try args.append(self.gpa, list);
                try args.appendSlice(self.gpa, initial);
                break :blk try b.loopOf(.for_list, args.items, body, slot_tys);
            },
        };
        try self.settleLoop(loop, carried, slot_tys.len, 0);
    }

    /// Bind each carried `var` to the loop's output for its slot.
    fn settleLoop(self: *Reifier, loop: Ref, carried: *const Carried, outputs: usize, first: usize) Error!void {
        if (carried.binders.items.len == 0) return;
        const outs = try self.gpa.alloc(Ref, carried.binders.items.len);
        defer self.gpa.free(outs);
        for (outs, 0..) |*out, k| out.* = if (outputs == 1) loop else Ref.node(loop.nodeId(), @intCast(first + k));
        try carried.rebind(self, outs);
    }

    /// What a loop body binds on entry.
    const Entry = union(enum) {
        /// The element or index the `for` pattern names.
        item: Test,
        /// A `while`: the condition, tested at the top of each turn.
        cond: CheckedExprId,
        /// A general loop: the iterator protocol's step.
        step: struct { plan: static_dispatch.IteratorForPlan, pattern: CheckedPatternId },
        /// A loop that runs until it breaks.
        none,
    };

    /// Build a loop body, which `loop.body` is and which is open: bind the
    /// slots, walk the turn, and end it in `Continue` with the next slots.
    fn loopBody(self: *Reifier, loop: Loop, carried: *const Carried, body_id: CheckedExprId, entry: Entry, region: base.Region) Error!void {
        const outer = self.loop;
        self.loop = loop;
        defer self.loop = outer;
        const scope_base = self.scope.items.len;
        defer self.scope.shrinkRetainingCapacity(scope_base);
        const slot_values = try self.gpa.alloc(Ref, carried.binders.items.len);
        defer self.gpa.free(slot_values);
        const first = loop.slot_base + @intFromBool(loop.iterator);
        for (slot_values, 0..) |*value, k| value.* = Ref.regionParam(loop.body, @intCast(first + k));
        try carried.rebind(self, slot_values);

        self.turn(loop, body_id, entry, region) catch |err| switch (err) {
            error.Diverged => return,
            error.Rejected, error.OutOfMemory => |e| return e,
        };
    }

    fn turn(self: *Reifier, loop: Loop, body_id: CheckedExprId, entry: Entry, region: base.Region) Error!void {
        switch (entry) {
            .item => |item| {
                try self.bindPattern(item.pattern, item.value);
                return self.continueTurn(loop, body_id, null, region);
            },
            .none => return self.continueTurn(loop, body_id, null, region),
            .cond => |cond_id| return self.whileTurn(loop, cond_id, body_id, region),
            .step => |step| return self.stepTurn(loop, step.plan, step.pattern, body_id, region),
        }
    }

    /// Walk the body, then end the turn with the next slots.
    fn continueTurn(self: *Reifier, loop: Loop, body_id: CheckedExprId, iterator: ?Ref, region: base.Region) Error!void {
        try self.discard(body_id);
        const next = try self.slotValues(loop, iterator, region);
        defer self.gpa.free(next);
        try self.terminate(.{ .continue_ = next });
    }

    /// `while cond { body }`: a `Bool` switch on the condition at the top of
    /// the turn, whose `False` arm breaks with the slots as they stand.
    fn whileTurn(self: *Reifier, loop: Loop, cond_id: CheckedExprId, body_id: CheckedExprId, region: base.Region) Error!void {
        const b = self.bld();
        const cond = try self.exprRef(cond_id);
        if (b.knownKey(cond)) |key| {
            if (key == 1) return self.continueTurn(loop, body_id, null, region);
            const slots = try self.slotValues(loop, null, region);
            defer self.gpa.free(slots);
            try self.terminate(.{ .break_ = slots });
        }
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        arms[0] = try b.openArm(cond, 0);
        {
            const slots = try self.slotValues(loop, null, region);
            defer self.gpa.free(slots);
            try b.close(.{ .break_ = slots });
        }
        arms[1] = try b.openArm(cond, 1);
        try closedTurn(self.continueTurn(loop, body_id, null, region));
        self.scope.shrinkRetainingCapacity(scope_base);
        const sw = try b.exitingSwitch(cond, &arms, &.{}, &.{});
        try self.terminate(.{ .branch = sw });
    }

    /// A turn of a general loop: `next` on the iterator slot, and a switch on
    /// the step's tags. `Done` breaks; `One` binds the item, walks the body
    /// and continues with the rest; `Skip` continues with the rest.
    fn stepTurn(self: *Reifier, loop: Loop, plan: static_dispatch.IteratorForPlan, pattern_id: CheckedPatternId, body_id: CheckedExprId, region: base.Region) Error!void {
        const b = self.bld();
        const iterator = Ref.regionParam(loop.body, loop.slot_base);
        const step = try self.readable(try self.dispatchWith(.{
            .method = plan.next.method,
            .dispatcher_ty = plan.next.dispatcher_ty,
            .resolution = plan.next.resolution,
        }, &.{iterator}, plan.step_ty, region));
        const step_ty = self.irs().refTy(b.row, step);
        const topology = plan.step_topology;
        const done = try self.tagName(step_ty, self.names.tagLabelText(topology.done_tag), region);
        const one = try self.tagName(step_ty, self.names.tagLabelText(topology.one_tag), region);
        const skip = try self.tagName(step_ty, self.names.tagLabelText(topology.skip_tag), region);
        const variants = switch (self.rt().get(step_ty)) {
            .tag_union => |span| span.len,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => invariant("an iterator step is not a tag union"),
        };
        if (variants != 3) invariant("an iterator step has other than three variants");
        const scope_base = self.scope.items.len;
        var arms: [3]RegionId = undefined;
        const members = try self.memberNames(step_ty, region);
        defer self.gpa.free(members);
        for (&arms, members) |*arm, member| {
            arm.* = try b.openTagArm(step, member);
            if (member == done) {
                const slots = try self.slotValues(loop, iterator, region);
                defer self.gpa.free(slots);
                try b.close(.{ .break_ = slots });
            } else if (member == one) {
                const payload = try self.readable(try b.payload(step, one, 0));
                const item = try b.field(payload, try self.fieldIndex(payload, self.names.recordFieldLabelText(topology.item_field), region));
                const rest = try b.field(payload, try self.fieldIndex(payload, self.names.recordFieldLabelText(topology.rest_field), region));
                try closedTurn(self.itemTurn(loop, pattern_id, item, body_id, rest, region));
            } else if (member == skip) {
                const payload = try self.readable(try b.payload(step, skip, 0));
                const rest = try b.field(payload, try self.fieldIndex(payload, self.names.recordFieldLabelText(topology.rest_field), region));
                const slots = try self.slotValues(loop, rest, region);
                defer self.gpa.free(slots);
                try b.close(.{ .continue_ = slots });
            } else unreachable; // a step union has exactly the done, one and skip variants (checked above)
            self.scope.shrinkRetainingCapacity(scope_base);
        }
        const sw = try b.exitingSwitch(step, &arms, &.{}, &.{});
        try self.terminate(.{ .branch = sw });
    }

    fn itemTurn(self: *Reifier, loop: Loop, pattern_id: CheckedPatternId, item: Ref, body_id: CheckedExprId, rest: Ref, region: base.Region) Error!void {
        try self.bindPattern(pattern_id, item);
        return self.continueTurn(loop, body_id, rest, region);
    }

    /// An arm of a turn closed itself, as every turn's does.
    fn closedTurn(result: Error!void) Error!void {
        result catch |err| switch (err) {
            error.Diverged => return,
            error.Rejected, error.OutOfMemory => |e| return e,
        };
        invariant("a turn ended without closing its region");
    }

    /// A loop over the iterator protocol: `iter` on the iterable, then a
    /// `Loop` whose first slot is the iterator.
    fn iteratorLoop(self: *Reifier, plan: static_dispatch.IteratorForPlan, pattern_id: CheckedPatternId, body_id: CheckedExprId, carried: *const Carried, region: base.Region) Error!void {
        const b = self.bld();
        const operands = plan.iter.argsSlice(self.plans);
        const iter_args = try self.gpa.alloc(Ref, operands.len);
        defer self.gpa.free(iter_args);
        for (operands, iter_args) |operand, *arg| arg.* = switch (operand) {
            .checked_expr => |child| try self.exprRef(child),
            .loop_iterator_state => invariant("iter reads the loop's iterator before the loop"),
        };
        const iterator = try self.dispatchWith(.{
            .method = plan.iter.method,
            .dispatcher_ty = plan.iter.dispatcher_ty,
            .resolution = plan.iter.resolution,
        }, iter_args, plan.iterator_ty, region);
        const initial = try self.slotValues(.{ .body = RegionId.none, .slot_base = 0, .iterator = true, .carried = carried.binders.items }, iterator, region);
        defer self.gpa.free(initial);
        const slot_tys = try self.gpa.alloc(TyId, initial.len);
        defer self.gpa.free(slot_tys);
        for (initial, slot_tys) |value, *ty| ty.* = self.irs().refTy(b.row, value);
        const body = try b.openRegion(.loop_body, slot_tys);
        try self.loopBody(.{ .body = body, .slot_base = 0, .iterator = true, .carried = carried.binders.items }, carried, body_id, .{ .step = .{ .plan = plan, .pattern = pattern_id } }, region);
        const loop = try b.loopOf(.loop, initial, body, slot_tys);
        try self.settleLoop(loop, carried, slot_tys.len, 1);
    }

    /// `while cond { body }` and the loops that run until they break: a
    /// `Loop` over the carried `var`s (N11d, N11e).
    fn conditionLoop(self: *Reifier, cond_id: CheckedExprId, body_id: CheckedExprId, mutations: ?checked.LoopMutationPlanId, tests: bool, region: base.Region) Error!void {
        const b = self.bld();
        var carried: Carried = .{};
        defer carried.deinit(self.gpa);
        try self.loopCarried(mutations, &.{ cond_id, body_id }, &carried);
        const shape: Loop = .{ .body = RegionId.none, .slot_base = 0, .iterator = false, .carried = carried.binders.items };
        const initial = try self.slotValues(shape, null, region);
        defer self.gpa.free(initial);
        const slot_tys = try self.gpa.alloc(TyId, initial.len);
        defer self.gpa.free(slot_tys);
        for (initial, slot_tys) |value, *ty| ty.* = self.irs().refTy(b.row, value);
        const body = try b.openRegion(.loop_body, slot_tys);
        var loop = shape;
        loop.body = body;
        try self.loopBody(loop, &carried, body_id, if (tests) .{ .cond = cond_id } else .none, region);
        const node = try b.loopOf(.loop, initial, body, slot_tys);
        try self.settleLoop(node, &carried, slot_tys.len, 0);
    }

    // Calls //

    /// A function of another package, named by owner and method (N8h). For a
    /// method the owner is its type's name; for a plain function, its
    /// module's.
    const ForeignName = struct { owner: []const u8, method: []const u8 };

    /// A plain call, `f(x)`: `Call` of the callee's row, a `Prim` for a
    /// builtin or a function of another package, or the derived codec or
    /// curried definition the call runs, folded into one node.
    fn callExpr(
        self: *Reifier,
        func: CheckedExprId,
        operands: []const CheckedExprId,
        result_ty: CheckedTypeId,
        demanded: ?TyId,
        region: base.Region,
    ) Error!Ref {
        // `Str.inspect` has no body to name, because the compiler writes the
        // rendering, so it is recognised by the intrinsic the checker recorded
        // for this use rather than resolved as a callee.
        if (self.calleeIntrinsic(func)) |intrinsic| {
            if (intrinsic == .str_inspect and operands.len == 1) return self.inspectExpr(operands[0], result_ty, region);
        }
        if (try self.foldedCodecExpr(func, operands, result_ty, region)) |folded| return folded;
        // The type the site reads the result at: the one its consumer demands,
        // or the checker's own for the call.
        const at = demanded orelse try self.tyOf(result_ty, region);
        if (try self.curriedCall(func, operands, at, region)) |flattened| return flattened;
        const inline_call = try self.walksInline(result_ty, region);
        self.walk.open_builtins = inline_call;
        var callee = self.calleeTarget(func, region) catch |err| {
            self.walk.open_builtins = false;
            return err;
        };
        self.walk.open_builtins = false;
        switch (callee) {
            .provided => |provided| {
                const args = try self.exprRefs(operands);
                defer self.gpa.free(args);
                return self.providedPrim(provided, args, result_ty, region);
            },
            .foreign => |name| {
                const args = try self.exprRefs(operands);
                defer self.gpa.free(args);
                const b = self.bld();
                return b.primOf(try b.namedPrim(name.owner, name.method), args, try self.tyOf(result_ty, region));
            },
            .value => {
                const f = try self.exprRef(func);
                const args = try self.exprRefs(operands);
                defer self.gpa.free(args);
                if (try self.appliedInline(f, args, at, region)) |applied| return applied;
                return self.bld().apply(f, args, try self.tyOf(result_ty, region));
            },
            .definition => {},
        }
        // The callee reference is the instantiation edge the checker keyed its
        // evidence by, so the answer to every `where` obligation of the callee
        // is in hand here and nowhere inside the body.
        if (self.plans.siteEvidence(func)) |supplied| {
            callee.definition.evidence = try self.supply(supplied, self.evidence);
        }
        if (inline_call) {
            const args = try self.exprRefs(operands);
            defer self.gpa.free(args);
            return self.inlineCall(callee.definition, args, at, region);
        }
        // A function argument the call fixes to a definition is no argument
        // of the row: the parameter binds to the definition, and the row is
        // keyed by it as well as by the types.
        try self.bindCallees(&callee.definition, operands, region);
        const kept = try self.keptOperands(operands, callee.definition.bound);
        defer self.gpa.free(kept);
        return self.callOf(callee.definition, &.{.{ .reader = self, .exprs = kept }}, at);
    }

    /// `Call` of a definition's row over what it captured, read here, then
    /// the argument groups the site wrote. Takes the callee's instantiation
    /// and bound callees. The call has the type `at` the site reads its result
    /// at, which is wider than the row's result where the site reads a
    /// narrower union at a wider one (design.md "Row Coercion Primitive").
    fn callOf(self: *Reifier, target: CalleeTarget, groups: []const ArgumentGroup, at: TyId) Error!Ref {
        var args = std.ArrayList(Ref).empty;
        defer args.deinit(self.gpa);
        // The callee was resolved where the first group is written, so that
        // is where what it captured is read.
        const owner = groups[0].reader;
        for (target.captures) |capture| {
            if (capturedCallee(target.bound, capture.pattern) != null) continue;
            const pattern = owner.bodies.pattern(capture.pattern);
            try args.append(self.gpa, try owner.lookupRef(capture.pattern, null, pattern.ty, null, null, pattern.source_region));
        }
        for (groups) |group| for (group.exprs) |child| {
            try args.append(self.gpa, try group.reader.exprRef(child));
        };
        const row = try self.calledRow(target);
        return self.bld().callRowAt(row, args.items, at);
    }

    /// The arguments of one group of a call, with the reader of the module
    /// that wrote them. A curried call's two groups can be written in two
    /// modules: a top-level value that computes a function is written in the
    /// module that defines it, and the call that runs it in the module that
    /// uses it.
    const ArgumentGroup = struct {
        reader: *Reifier,
        exprs: []const CheckedExprId,
    };

    /// A builtin by its export name, `Builtin.Num.I64.plus`: the `Prim` of
    /// its owner and method (N1a).
    fn providedPrim(self: *Reifier, provided: Provided, args: []const Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const name = prims.namedOfExport(provided.name) orelse
            return self.rejectError(.unresolved_reference, region, "a builtin with no owner in its name");
        const b = self.bld();
        return b.primOf(try b.namedPrimWithRole(name.owner, name.method, provided.role), args, try self.tyOf(result_ty, region));
    }

    /// The expression that constructed a function, and the reader of the
    /// module that wrote it.
    const Constructor = struct {
        reader: *Reifier,
        expr: CheckedExprId,
    };

    /// The call one expression constructed a function with: the call itself,
    /// the one a held binding remembers, or the definition of a top-level
    /// value that computes the function.
    fn constructorCall(self: *Reifier, func: CheckedExprId, region: base.Region) Error!?Constructor {
        const callee = self.bodies.expr(func);
        switch (callee.data) {
            .lookup_local => |local| {
                const binder = self.bodies.patternBinderForCheckedPattern(local.pattern) orelse
                    return null;
                const binding = self.lookupBinding(binder) orelse return self.computedConstructor(local.resolved, region);
                return switch (binding.kind) {
                    .function => |bound| if (self.lambdaOf(bound) == null) .{ .reader = self, .expr = bound } else null,
                    .value, .constant, .callee => null,
                };
            },
            .lookup_external, .lookup_required => |reference| return self.computedConstructor(reference, region),
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
            => return if (self.constructsFunction(func)) .{ .reader = self, .expr = func } else null,
        }
    }

    /// What a top-level value that computes a function was written as, where
    /// the name is such a value of a module the walk reads.
    fn computedConstructor(self: *Reifier, resolved: ?checked.ResolvedValueRefId, region: base.Region) Error!?Constructor {
        const id = resolved orelse return null;
        const computed = try self.computedFunction(id, region) orelse return null;
        const written = switch (computed) {
            .written => |written| written,
            // A function of another package has no body here to flatten.
            .foreign => return null,
        };
        // A value written as another such value, `renamed = doubler`, is the
        // one it names. The definition is marked while the walk follows it, so
        // a value that reaches itself ends at its own definition.
        const data = written.reader.bodies.expr(written.body).data;
        const named: ?checked.ResolvedValueRefId = if (data == .lookup_local)
            data.lookup_local.resolved
        else if (data == .lookup_external)
            data.lookup_external
        else if (data == .lookup_required)
            data.lookup_required
        else
            null;
        if (named != null and !written.reader.folding.contains(written.body)) {
            try written.reader.folding.put(written.reader.gpa, written.body, {});
            defer _ = written.reader.folding.remove(written.body);
            if (try written.reader.computedConstructor(named, region)) |inner| return inner;
        }
        return .{ .reader = written.reader, .expr = written.body };
    }

    /// One `Call` for a definition that hands back a function and a use that
    /// runs it: the row gathers both lambdas' parameters, the constructor's
    /// arguments come first and the applied ones after (N8a).
    ///
    /// Null when the callee is not a curried definition, which is every other
    /// call.
    fn curriedCall(self: *Reifier, func: CheckedExprId, operands: []const CheckedExprId, at: TyId, region: base.Region) Error!?Ref {
        const constructor = try self.constructorCall(func, region) orelse return null;
        // The constructor is read where it was written. For a name bound in
        // the row that is this reader, and for a top-level value it is the
        // reader of the module that defines the value.
        const writer = constructor.reader;
        const built = writer.bodies.expr(constructor.expr).data;
        if (built == .call) {
            const call = built.call;
            const resolved = try writer.calleeTarget(call.func, region);
            if (resolved != .definition) return null;
            var callee = resolved.definition;
            if (writer.plans.siteEvidence(call.func)) |supplied| {
                callee.evidence = try writer.supply(supplied, writer.evidence);
            }
            return self.flattenedCall(callee, .{ .reader = writer, .exprs = call.args }, operands, at);
        }
        if (built != .dispatch_call and built != .type_dispatch_call) return null;
        const id = (if (built == .dispatch_call) built.dispatch_call else built.type_dispatch_call) orelse return null;
        const plan = writer.plans.plans[@backingInt(id)];
        const found = try writer.dispatchTarget(DispatchSpec.ofPlan(plan), region);
        const callee = switch (found) {
            .definition => |target| target,
            // A builtin or a function of another package carries no body to
            // flatten a curried call through.
            .provided, .foreign, .none => return null,
        };
        const constructed = try writer.dispatchExprs(plan, region);
        defer self.gpa.free(constructed);
        return self.flattenedCall(callee, .{ .reader = writer, .exprs = constructed }, operands, at);
    }

    /// One `Call` over both argument groups, against the row that gathers
    /// both lambdas' parameters. Takes the callee's instantiation either way.
    fn flattenedCall(self: *Reifier, callee: CalleeTarget, constructed: ArgumentGroup, operands: []const CheckedExprId, at: TyId) Error!?Ref {
        var target = callee;
        if (!target.reader.isCurried(target.key.body)) {
            if (target.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
            return null;
        }
        target.key.curried = true;
        return try self.callOf(target, &.{ constructed, .{ .reader = self, .exprs = operands } }, at);
    }

    /// One dispatch's operands as checked expressions. The caller owns the
    /// slice.
    fn dispatchExprs(self: *Reifier, plan: static_dispatch.StaticDispatchCallPlan, region: base.Region) Error![]CheckedExprId {
        const operands = plan.argsSlice(self.plans);
        const ids = try self.gpa.alloc(CheckedExprId, operands.len);
        errdefer self.gpa.free(ids);
        for (operands, ids) |operand, *id| id.* = switch (operand) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments => return self.rejectError(.unsupported_expression, region, "a compiler-generated argument"),
        };
        return ids;
    }

    /// Resolve every function argument this call passes to the definition it
    /// names, and key the callee's row by them.
    ///
    /// A function chosen by an `if`, read out of a record or taken from a
    /// list names no definition, and neither does a lambda that captures: the
    /// row is built on its own, where a capture of the caller's scope has
    /// nothing to read. Each is passed as a value, and a call of it in the
    /// callee is an `Apply`, which a known closure resolves once the caller
    /// is simplified (N8i).
    fn bindCallees(self: *Reifier, target: *CalleeTarget, operands: []const CheckedExprId, region: base.Region) Error!void {
        // A lifted lambda arrives with the names it captured already bound.
        var bound = std.ArrayList(BoundCallee).fromOwnedSlice(target.bound);
        target.bound = &.{};
        errdefer {
            self.releaseBound(bound.items);
            bound.deinit(self.gpa);
        }
        const before = bound.items.len;
        for (operands, 0..) |operand, index| {
            if (self.functionOf(self.bodies.expr(operand).ty) == null) continue;
            const passed = try self.passedArgument(operand, region) orelse continue;
            try bound.append(self.gpa, .{ .param = .{ .position = @intCast(index) }, .target = passed });
        }
        if (bound.items.len != before) target.key.callees = boundCalleesKey(bound.items);
        target.bound = try bound.toOwnedSlice(self.gpa);
    }

    /// The definition one function argument names: a name the caller wrote,
    /// or the row a lambda written at the site lifts into. A template's
    /// argument must name one.
    fn passedCallee(self: *Reifier, operand: CheckedExprId, region: base.Region) Error!CalleeTarget {
        if (self.lambdaOf(operand) != null and self.capturesOf(operand).len != 0) {
            return self.rejectError(.capture, region, self.capturedName(self.capturesOf(operand)[0].pattern));
        }
        return try self.passedArgument(operand, region) orelse
            self.rejectError(.unsupported_expression, region, "a function value that names no definition");
    }

    /// The definition one function argument of a call names, or null for a
    /// function the call passes as a value: a lambda that captures, or one
    /// that names no definition.
    fn passedArgument(self: *Reifier, operand: CheckedExprId, region: base.Region) Error!?CalleeTarget {
        if (self.lambdaOf(operand) != null) {
            // A lambda that captures only names a call fixed captures no
            // value: it is the definitions those names stand for.
            const captures = self.capturesOf(operand);
            for (captures) |capture| {
                if (self.calleeInScope(capture.pattern) == null) return null;
            }
            return try self.enclosedLambda(operand, null, captures);
        }
        return switch (try self.calleeTarget(operand, region)) {
            .definition => |definition| definition,
            .value => null,
            .provided, .foreign => self.rejectError(.unsupported_expression, region, "a builtin or a function of another package, passed as an argument"),
        };
    }

    /// Which definitions a call fixed a callee's function parameters to,
    /// digested so two calls at one set of definitions share a row and two at
    /// different ones take one each.
    fn boundCalleesKey(bound: []const BoundCallee) [32]u8 {
        var hasher = std.crypto.hash.Blake3.init(.{});
        for (bound) |entry| {
            switch (entry.param) {
                .position => |position| {
                    hasher.update(&[_]u8{0});
                    hasher.update(std.mem.asBytes(&position));
                },
                .capture => |pattern| {
                    hasher.update(&[_]u8{1});
                    hasher.update(std.mem.asBytes(&pattern));
                },
            }
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
    /// function parameter. The caller owns the slice.
    fn keptOperands(self: *Reifier, operands: []const CheckedExprId, bound: []const BoundCallee) Allocator.Error![]CheckedExprId {
        var kept = std.ArrayList(CheckedExprId).empty;
        errdefer kept.deinit(self.gpa);
        for (operands, 0..) |operand, index| {
            if (fixesCallee(bound, index)) continue;
            try kept.append(self.gpa, operand);
        }
        return kept.toOwnedSlice(self.gpa);
    }

    /// Whether one argument position fixed a function parameter.
    fn fixesCallee(bound: []const BoundCallee, index: usize) bool {
        for (bound) |entry| {
            switch (entry.param) {
                .position => |position| if (position == index) return true,
                .capture => {},
            }
        }
        return false;
    }

    /// What a plain call's callee names, or a refusal naming why it names
    /// nothing.
    ///
    /// The lookup form says where the name was written; the resolved reference
    /// says what it reached. So a `lookup_local` the scope holds is a binding,
    /// and everything else is decided by the reference.
    fn calleeTarget(self: *Reifier, func: CheckedExprId, region: base.Region) Error!Callee {
        const callee = self.bodies.expr(func);
        if (callee.data == .lookup_local) {
            const local = callee.data.lookup_local;
            const binder = self.bodies.patternBinderForCheckedPattern(local.pattern) orelse
                return self.rejectError(.unresolved_reference, region, "this call");
            if (self.lookupBinding(binder)) |binding| return self.liftedTarget(binding, callee.ty, func, region);
            if (try self.replayBinding(binder)) |binding| return self.liftedTarget(binding, callee.ty, func, region);
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
            => return .value,
        };
        return self.resolvedTarget(resolved, null, region);
    }

    /// A lambda the block bound, lifted into a row of its own (N8b), or the
    /// definition a call fixed a parameter to.
    ///
    /// A lambda the block generalized is built at the type `use`, the type
    /// the lookup instantiated its scheme to, so each type it is called at
    /// keys a row of its own.
    fn liftedTarget(self: *Reifier, binding: Binding, use: CheckedTypeId, use_expr: ?CheckedExprId, region: base.Region) Error!Callee {
        const bound = switch (binding.kind) {
            .function => |expr_id| expr_id,
            .callee => |index| return .{ .definition = try self.boundTarget(self.bound[index].target) },
            .value, .constant => return .value,
        };
        if (self.lambdaOf(bound) == null) return .value;
        const instance = if (self.localScheme(bound)) |scheme|
            try self.instantiationOf(scheme, self, use, use_expr, region, .call)
        else
            null;
        return .{ .definition = try self.enclosedLambda(bound, instance, self.capturesOf(bound)) };
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

    /// What a resolved reference reaches: a definition and the reader that
    /// walks it, a builtin, or a function of another package.
    ///
    /// Every hop is a ref the producer recorded: the reference names a
    /// binding, the binding names a template, and the template holds the body.
    ///
    /// `written_binder` is what the call site's own name binds, which names a
    /// definition of this module.
    fn resolvedTarget(self: *Reifier, resolved: checked.ResolvedValueRefId, written_binder: ?PatternBinderId, region: base.Region) Error!Callee {
        // A top-level value that computes a function is no definition. A call
        // on it is the call of the definition it is written as when that is a
        // curried call (`curriedCall`), and otherwise an `Apply` of the value
        // it is written as, which the builder resolves once the value is a
        // known closure.
        if (try self.computedFunction(resolved, region)) |computed| return switch (computed) {
            .written => .value,
            .foreign => |name| .{ .foreign = name },
        };
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
            => return .value,
        };
        const reached = try self.reachedProcedure(use.binding, written_binder, region);
        const reader = reached.reader;
        // A definition of another module is a builtin by its export name, a
        // function of another package by its module and name (N8h), and
        // otherwise the definition to walk.
        // A builtin is named wherever it is called, the builtin module's own
        // bodies included. A first stage walks the Roc definition of a
        // builtin that hands back a function, and names every other.
        if (reader.env.module_role == .builtin) {
            if (!self.walk.open_builtins) {
                const export_name = providedName(reader.names, reached.template) orelse
                    return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides");
                return .{ .provided = .{ .name = export_name.text, .role = roleOf(use.iterator_procedure) } };
            }
        } else if (!std.meta.eql(reader.artifact.bytes, self.artifact.bytes) and !samePackage(self.env, reader.env)) {
            const binder = reached.binder orelse return reader.rejectError(.unresolved_reference, region, "this call");
            return .{ .foreign = .{ .owner = reader.env.module_name, .method = reader.binderName(binder) } };
        }
        // What the use copied the procedure's variables to is keyed by the
        // use, and only a use of the procedure's own scheme has it.
        const written = self.value_refs.records[@backingInt(resolved)];
        const use_expr = if (reached.forwarded or written.ref == .local_proc) null else written.expr;
        var instance = try reader.instantiationOf(reader.templateScheme(reached.template), self, use.source_fn_ty_payload, use_expr, region, .call);
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        return .{ .definition = .{
            .key = .{
                .artifact = reader.artifact.bytes,
                .body = reached.body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .reader = reader,
            .instantiation = instance,
        } };
    }

    /// The procedure a binding names, with every exact alias on the way
    /// followed: the reader of the module that defines it, its body, and its
    /// template.
    const ReachedProcedure = struct {
        reader: *Reifier,
        body: CheckedExprId,
        template: checked.CheckedProcedureTemplate,
        /// What the procedure's own name binds in `reader`'s module. A call
        /// to a function of another package names the function by it.
        binder: ?PatternBinderId,
        /// Whether an exact alias was followed to get here. A use then
        /// instantiates the alias's scheme, not the procedure's.
        forwarded: bool = false,
    };

    fn reachedProcedure(
        self: *Reifier,
        binding: checked.ProcedureBindingRef,
        written_binder: ?PatternBinderId,
        region: base.Region,
    ) Error!ReachedProcedure {
        return switch (binding) {
            .top_level => |top_level| self.reachedHere(top_level, written_binder, region),
            .imported => |imported| self.reachedAway(imported, region),
            .hosted => self.rejectError(.unsupported_expression, region, "a call to a function the host provides"),
            .platform_required => self.rejectError(.unsupported_expression, region, "a call to a function the platform requires"),
        };
    }

    /// A procedure of the module being walked.
    fn reachedHere(
        self: *Reifier,
        binding_ref: checked.ArtifactTopLevelProcedureBindingRef,
        written_binder: ?PatternBinderId,
        region: base.Region,
    ) Error!ReachedProcedure {
        if (!std.meta.eql(binding_ref.artifact.bytes, self.artifact.bytes)) {
            return self.rejectError(.unresolved_reference, region, "this call");
        }
        const binder = written_binder orelse return self.rejectError(.unresolved_reference, region, "this call");
        const template_ref = switch (self.procedure_bindings.get(binding_ref.binding).body) {
            .direct_template => |direct| switch (direct.template) {
                .checked => |template| template,
                .lifted, .synthetic => return self.rejectError(.unresolved_reference, region, "this call"),
            },
            // A top-level value whose definition computes a function. The
            // checker records the lookup an exact alias of a function,
            // `same = add_one`, forwards to, and that lookup names the
            // procedure. Any other such value reaches here only as the
            // function a site itself names: a use inside a description is
            // read as the definition (`computedFunction`), but a site's root
            // needs a lambda whose parameters it can list, and a value that
            // computes a function has none.
            .callable_eval_template => |id| {
                const lookup = self.callable_eval_templates.templates[@backingInt(id)].forwarded_lookup orelse
                    return self.rejectError(.unsupported_expression, region, "a top-level constant that computes a function, named as the function to describe");
                return self.forwardedProcedure(lookup, region);
            },
            .checked_error => return self.rejectError(.unresolved_reference, region, "this call"),
        };
        const templates = self.procedure_templates.templates.items;
        const raw = @backingInt(template_ref.template);
        if (raw >= templates.len) return self.rejectError(.unresolved_reference, region, "this call");
        const template = templates[raw];
        const body = switch (template.body) {
            .checked_body => |body_id| self.bodies.body(body_id).root_expr,
            .intrinsic_wrapper, .entry_wrapper, .unimplemented => return self.rejectError(.unresolved_reference, region, "this call"),
        };
        return .{ .reader = self, .body = body, .template = template, .binder = binder };
    }

    /// A procedure of a module this one reaches through an import, or the
    /// procedure an exact alias that module exports forwards to.
    fn reachedAway(
        self: *Reifier,
        binding_ref: checked.ImportedProcedureBindingRef,
        region: base.Region,
    ) Error!ReachedProcedure {
        if (self.walk.foreign.findExported(binding_ref.artifact, binding_ref.def)) |definition| {
            const reader = try self.walk.reader(definition.module);
            return .{
                .reader = reader,
                .body = definition.body,
                .template = definition.template,
                .binder = reader.bodies.patternBinderForCheckedPattern(binding_ref.pattern),
            };
        }
        const alias = self.walk.foreign.findExportedAlias(binding_ref.artifact, binding_ref.def) orelse
            return self.rejectError(.unsupported_expression, region, "a call to a function in a module this one does not read");
        const reader = try self.walk.reader(alias.module);
        return reader.forwardedProcedure(alias.lookup, region);
    }

    /// The procedure the lookup an exact alias forwards to names. The
    /// checker forwards an alias only to a lookup of a procedure it can call
    /// directly, and an alias of an alias only once that alias forwards, so
    /// the hops end.
    fn forwardedProcedure(self: *Reifier, lookup: CheckedExprId, region: base.Region) Error!ReachedProcedure {
        const resolved = self.value_refs.lookupIdByCheckedExpr(lookup) orelse
            invariant("an alias forwards to a lookup with no resolved reference");
        const use = switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| use,
            .hosted_proc => return self.rejectError(.unsupported_expression, region, "a call to a function the host provides"),
            .platform_required_proc => return self.rejectError(.unsupported_expression, region, "a call to a function the platform requires"),
            .local_proc,
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
            => invariant("an alias forwards to a lookup that names no top-level procedure"),
        };
        const data = self.bodies.expr(lookup).data;
        const binder = if (data == .lookup_local) self.bodies.patternBinderForCheckedPattern(data.lookup_local.pattern) else null;
        var reached = try self.reachedProcedure(use.binding, binder, region);
        reached.forwarded = true;
        return reached;
    }

    /// A builtin the walk names instead of walking: its export name, and the
    /// role the checker gave it when it is a procedure of the iterator
    /// protocol (N11k).
    const Provided = struct {
        name: []const u8,
        role: ir.IteratorRole = .none,
    };

    /// The role of the iterator procedure the checker recorded, when the walk
    /// has a rule for it.
    fn roleOf(procedure: ?checked.IteratorProcedureId) ir.IteratorRole {
        return switch (procedure orelse return .none) {
            .identity => .identity,
            .next => .next,
            .list_iter => .list_iter,
            .custom, .single, .list_iter_rev, .str_iter_utf8, .map, .keep_if, .drop_if, .take_first, .drop_first, .concat, .append, .with_index, .step_by, .from_iter, .range_iter, .numeric_range_iter, .numeric_to, .numeric_until, .from_step, .range_done => .none,
        };
    }

    /// The name a function the compiler provides answers to.
    const ProvidedName = struct {
        id: canonical.ExportNameId,
        text: []const u8,
    };

    /// What a builtin is called: its export name, the one spelling the
    /// compiler holds for every builtin procedure. A procedure the builtin
    /// module does not export has none.
    fn providedName(names: *const canonical.CanonicalNameStore, template: checked.CheckedProcedureTemplate) ?ProvidedName {
        const proc_base = names.procBase(template.proc_base);
        const id = proc_base.export_name orelse return null;
        return .{ .id = id, .text = names.exportNameText(id) };
    }

    // Dispatch //

    /// What names a dispatch's target, which a planned call and the two
    /// calls of the iterator protocol all carry.
    const DispatchSpec = struct {
        method: canonical.MethodNameId,
        dispatcher_ty: CheckedTypeId,
        resolution: static_dispatch.CheckedCallResolution,

        fn ofPlan(plan: static_dispatch.StaticDispatchCallPlan) DispatchSpec {
            return .{ .method = plan.method, .dispatcher_ty = plan.dispatcher_ty, .resolution = plan.resolution };
        }
    };

    /// A static dispatch: `Call` of the method's row, a `Prim` for a builtin
    /// or a method of another package, or the derivation the checker chose.
    /// `!=` on a written `is_eq` is `Bool.not` of the call (N1k).
    fn dispatchExpr(self: *Reifier, plan_id: ?static_dispatch.StaticDispatchPlanId, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const id = plan_id orelse return self.rejectError(.unresolved_reference, region, "this call");
        const plan = self.plans.plans[@backingInt(id)];
        const value = try self.plannedDispatch(plan, result_ty, region);
        const negated = switch (plan.result_mode) {
            .equality => |eq| eq.negated,
            .value, .hash, .parser_for, .encoder_for, .map, .map_effectful => false,
        };
        return if (negated) self.bld().call(.bool_, .not, &.{value}) else value;
    }

    fn plannedDispatch(self: *Reifier, plan: static_dispatch.StaticDispatchCallPlan, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        switch (plan.resolution) {
            // The checker picked a compiler-derived implementation, so there is
            // no Roc body behind this name.
            .structural => |derivation| return self.structuralDispatch(plan, derivation, result_ty, region),
            .checked_error, .@"unreachable" => return self.rejectError(.unresolved_reference, region, "this call"),
            // The body forwards this obligation to its own evidence param, and
            // the call that instantiated the body says what discharged it.
            .evidence_dependent => |forwarded| {
                if (self.forwardedDerivation(forwarded.index)) |derivation| {
                    return self.structuralDispatch(plan, derivation, result_ty, region);
                }
            },
            .direct_pending, .direct_closed, .direct_parametric => {},
        }
        const operands = plan.argsSlice(self.plans);
        const args = try self.gpa.alloc(Ref, operands.len);
        defer self.gpa.free(args);
        var generated: Generated = .none;
        for (operands, args) |operand, *arg| arg.* = switch (operand) {
            .checked_expr => |child| try self.exprRef(child),
            .generated_numeral => |numeral_operand| blk: {
                generated = .{ .numeral = numeral_operand };
                break :blk try self.generatedNumeral(numeral_operand, region);
            },
            .generated_quote => |literal| blk: {
                generated = .quote;
                break :blk try self.bld().litStr(self.bodies.stringLiteral(literal));
            },
            .generated_interpolation_segments => invariant("an interpolation's plan is walked by its literal"),
        };
        return self.dispatchWithArgs(DispatchSpec.ofPlan(plan), args, generated, result_ty, region);
    }

    /// The `Num.Numeral` a row that converts a literal takes, of the nominal
    /// type `param` its parameter names: the `Literal` the compiler makes
    /// from the digits the literal spells, field by field as Monotype makes it
    /// (`lowerNumeralValue`).
    fn numeralArgument(self: *Reifier, literal: ModuleEnv.NumeralLiteral, param: TyId) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        const unfolded = switch (types.get(param)) {
            .nominal => try types.unfold(param),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => invariant("a from_numeral parameter is not the Numeral nominal"),
        };
        const literal_tag = types.findName("Literal") orelse invariant("the Numeral type has no Literal tag");
        const at = types.memberIndex(unfolded, literal_tag) orelse invariant("the Numeral type has no Literal tag");
        const record_ty = types.tySlice(types.memberSlice(types.get(unfolded).tag_union)[at].tys)[0];
        const fields = try self.gpa.dupe(reify.types.Member, types.memberSlice(types.get(record_ty).record));
        defer self.gpa.free(fields);
        const values = try self.gpa.alloc(Ref, fields.len);
        defer self.gpa.free(values);
        for (fields, values) |field, *value| {
            const label = types.nameText(field.name);
            const field_ty = types.tySlice(field.tys)[0];
            value.* = if (std.mem.eql(u8, label, "is_negative"))
                try b.litBool(literal.isNegative())
            else if (std.mem.eql(u8, label, "digits_before_pt"))
                try self.u8List(self.env.numeralDigitsBefore(literal), field_ty)
            else if (std.mem.eql(u8, label, "digits_after_pt"))
                try self.u8List(self.env.numeralDigitsAfter(literal), field_ty)
            else if (std.mem.eql(u8, label, "digits_after_pt_count"))
                try b.litInt(field_ty, literal.after_decimal_digit_count)
            else
                invariant("the Numeral record has a field the compiler does not fill");
        }
        const record = try b.record(record_ty, values);
        return b.wrap(param, try b.tag(unfolded, literal_tag, &.{record}));
    }

    /// A `List(U8)` of the bytes: the empty list, or one literal holding them.
    fn u8List(self: *Reifier, bytes: []const u8, ty: TyId) Error!Ref {
        if (bytes.len == 0) return self.bld().listOf(ty, &.{});
        return self.bld().litBytes(ty, bytes);
    }

    /// The value a conversion's `Try` holds: its `Ok` payload, or, where the
    /// conversion rejected the literal, the crash that rejection is when the
    /// program runs. That crash is the compiler's, not the author's, so it is
    /// a rejected literal's crash (`ir.CrashKind`), which N13w may drop.
    fn convertedLiteral(self: *Reifier, converted: Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        return self.convertedWith(converted, null, result_ty, region);
    }

    /// `convertedLiteral`, where the `Ok` payload is a function that the
    /// literal applies to `values`, an interpolated literal's list.
    fn convertedWith(self: *Reifier, converted: Ref, values: ?Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const b = self.bld();
        const ty = try self.tyOf(result_ty, region);
        const found = try self.readable(converted);
        const ok = try self.rt().name("Ok");
        const names = try self.memberNames(self.irs().refTy(b.row, found), region);
        defer self.gpa.free(names);
        const arms = try self.gpa.alloc(RegionId, names.len);
        defer self.gpa.free(arms);
        for (arms, names) |*arm, name| {
            arm.* = try b.openTagArm(found, name);
            const delivered = if (name == ok)
                if (values) |list| try b.apply(try b.payload(found, ok, 0), &.{list}, ty) else try b.payload(found, ok, 0)
            else
                try b.rejectedLiteral(ty, try b.litStr("this literal was rejected by its conversion"));
            try b.close(.{ .value = &.{delivered} });
        }
        return b.switchOn(found, arms, &.{}, &.{ty}, &.{});
    }

    /// The literal the compiler hands to a `from_numeral` conversion, in the
    /// widest form a `Lit` holds: `I128` for a whole number, `F64` for a
    /// fractional one. It is the argument only of a builtin or a method of
    /// another package, whose `Prim` takes it as the number it is.
    fn generatedNumeral(self: *Reifier, literal: ModuleEnv.NumeralLiteral, region: base.Region) Error!Ref {
        const exact = self.env.exactNumeral(literal);
        const primitive: checked.CheckedBuiltinNominal = if (exact.is_fractional) .f64 else .i128;
        const ty = if (exact.is_fractional) try self.rt().floatTy(.f64) else try self.rt().intTy(.i128);
        return self.numeralLit(literal, primitive, ty, region);
    }

    /// A dispatch over operands already built.
    fn dispatchWith(self: *Reifier, spec: DispatchSpec, args: []const Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        return self.dispatchWithArgs(spec, args, .none, result_ty, region);
    }

    /// The operand of a literal's conversion that the compiler wrote, which
    /// makes the dispatch a conversion of a literal.
    const Generated = union(enum) {
        none,
        /// The number the literal spells.
        numeral: ModuleEnv.NumeralLiteral,
        /// The text between the quotes, a `Str`.
        quote,
    };

    /// `generated` says an operand is one the compiler wrote. A `Prim` takes
    /// it as the number or text it is. A row's parameter has the type the
    /// method declares, so a `Num.Numeral` is built for it
    /// (`numeralArgument`), and the row's `Try` is read as the checker reads
    /// a conversion: the `Ok` payload is the literal's value, and an `Err`
    /// is a literal the conversion rejected.
    fn dispatchWithArgs(self: *Reifier, spec: DispatchSpec, args: []const Ref, generated: Generated, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const b = self.bld();
        const inline_call = generated == .none and try self.walksInline(result_ty, region);
        self.walk.open_builtins = inline_call;
        const found = self.dispatchTarget(spec, region) catch |err| {
            self.walk.open_builtins = false;
            return err;
        };
        self.walk.open_builtins = false;
        switch (found) {
            .definition => |target| {
                if (inline_call) return self.inlineCall(target, args, null, region);
                // A method takes no captures, so its row's parameters are the
                // dispatch's operands.
                const row = try self.calledRow(target);
                switch (generated) {
                    .none => return b.callRow(row, args),
                    .quote => return self.convertedLiteral(try b.callRow(row, args), result_ty, region),
                    .numeral => |literal| {
                        const param = self.irs().tySlice(self.irs().row(row).params)[0];
                        const converted = try b.callRow(row, &.{try self.numeralArgument(literal, param)});
                        return self.convertedLiteral(converted, result_ty, region);
                    },
                }
            },
            .provided => |provided| return self.providedPrim(provided, args, result_ty, region),
            .foreign => |name| return b.primOf(try b.namedPrim(name.owner, name.method), args, try self.tyOf(result_ty, region)),
            .none => return self.rejectError(.unresolved_reference, region, "a method this call names no target for"),
        }
    }

    /// One instantiation edge: the target the checker chose, and the reader of
    /// the module that recorded it.
    const DispatchEdge = struct {
        reader: *Reifier,
        node: static_dispatch.EvidenceNode,
        /// The evidence the walk held where the edge was recorded, which the
        /// node's nested evidence forwards into.
        scope: SuppliedEvidence,
    };

    /// The instantiation edge this dispatch was discharged through, or null
    /// when nothing names a target.
    fn dispatchEdge(self: *Reifier, resolution: static_dispatch.CheckedCallResolution) ?DispatchEdge {
        switch (resolution) {
            .direct_closed, .direct_parametric => |direct| {
                return .{ .reader = self, .node = self.plans.evidenceNode(direct.evidence), .scope = self.evidence };
            },
            // The body forwards the obligation to its own evidence param, so
            // the target is named by the call that instantiated the body and
            // recorded in that call's own tables.
            .evidence_dependent => |forwarded| {
                if (forwarded.index.depth != 0) return null;
                if (forwarded.index.index >= self.evidence.entries.len) return null;
                const entry = self.evidence.entries[forwarded.index.index];
                return switch (entry.evidence.resolution) {
                    .direct => |node_id| .{ .reader = entry.reader, .node = entry.reader.plans.evidenceNode(node_id), .scope = entry.scope },
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
        /// A body the walk builds a row for.
        definition: CalleeTarget,
        /// A builtin, by its export name.
        provided: Provided,
        /// A method of another package (N8h), or of an opaque nominal.
        foreign: ForeignName,
        /// Nothing the walk reaches.
        none,
    };

    fn dispatchTarget(self: *Reifier, spec: DispatchSpec, region: base.Region) Error!DispatchCallee {
        const method = self.names.methodNameText(spec.method);
        if (self.dispatchEdge(spec.resolution)) |edge| {
            return self.methodTargetCallee(edge.reader, edge.node.target, .{ .edge = edge }, method, spec.dispatcher_ty, region);
        }
        // A body the compiler's own derivation reached is fixed by its
        // receiver, and no call supplied evidence for what it forwards. The
        // receiver fixed the dispatcher too, so the target is the method its
        // nominal declares, read from the registry the derivation read.
        if (spec.resolution == .evidence_dependent and self.evidence.reader == null) {
            const fixed = self.fixedType(spec.dispatcher_ty) orelse return .none;
            const nominal = fixed.reader.nominalOf(fixed.id) orelse return .none;
            const target = self.walk.foreign.findMethod(fixed.reader.foreignNominal(nominal), method) orelse return .none;
            return fixed.reader.methodTargetCallee(fixed.reader, target, .{ .receiver = fixed }, method, fixed.id, region);
        }
        return .none;
    }

    /// How a call fixes a method's quantified variables and discharges its
    /// obligations: off the dispatch's edge, or, for a method the compiler's
    /// own derivation reached, off the receiver's type.
    const MethodFixing = union(enum) {
        edge: DispatchEdge,
        receiver: TypeRef,
    };

    /// What one method target is from the walk's side.
    ///
    /// `owner` is the reader of the module that recorded the target, which is
    /// the module whose ids the target is named in; `dispatcher_ty` is the
    /// type the method is called on, whose name a method of another package
    /// is owned by.
    fn methodTargetCallee(
        self: *Reifier,
        owner: *Reifier,
        target: static_dispatch.MethodTarget,
        fixing: MethodFixing,
        method: []const u8,
        dispatcher_ty: CheckedTypeId,
        region: base.Region,
    ) Error!DispatchCallee {
        const procedure = switch (target.kind) {
            .procedure => |procedure| procedure,
            .local_proc, .structural => return .none,
        };
        // A method of an opaque nominal reads the representation the type
        // hides, and a stage is outside the type's module, so the method is
        // named rather than walked, as its values are.
        if (self.nominalOf(dispatcher_ty)) |nominal| {
            if (nominal.is_opaque and nominal.builtin == null) {
                return .{ .foreign = .{ .owner = self.names.typeNameText(nominal.name), .method = method } };
            }
        }
        const found = owner.methodDefinition(procedure.template, target.def_idx) orelse return .none;
        const reader = switch (found) {
            .provided => |builtin| if (self.walk.open_builtins)
                try self.walk.reader(builtin.definition.module)
            else
                return .{ .provided = .{ .name = builtin.name, .role = roleOf(procedure.runtime_target.iteratorProcedure()) } },
            .here => owner,
            .here_builtin => |builtin| if (self.walk.open_builtins)
                owner
            else
                return .{ .provided = .{ .name = builtin.name, .role = roleOf(procedure.runtime_target.iteratorProcedure()) } },
            .away => |definition| blk: {
                if (!samePackage(self.env, definition.module.env)) {
                    const type_name = self.typeName(dispatcher_ty) orelse
                        return self.rejectError(.unresolved_type, region, "the type a method of another package is called on");
                    return .{ .foreign = .{ .owner = type_name, .method = method } };
                }
                break :blk try self.walk.reader(definition.module);
            },
        };
        var instance = switch (fixing) {
            .edge => |edge| try owner.dispatchInstantiation(reader, found.template(), edge.node, region),
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
                .reader = reader,
                .instantiation = instance,
                .evidence = switch (fixing) {
                    .edge => |edge| switch (edge.node.nested) {
                        .resolved => try owner.supply(owner.plans.nestedEvidence(edge.node), edge.scope),
                        // The edge derives the target's evidence from its
                        // callable rather than recording it, so the walk of the
                        // body has no answer to read.
                        .from_callable => .{},
                    },
                    // A derivation records no evidence, because the checker
                    // planned no call.
                    .receiver => .{},
                },
            },
        };
    }

    /// Where a method's body lives: this module's tables, another module's
    /// export rows, or the builtin module, whose function carries its name.
    const MethodDefinition = union(enum) {
        here: struct { template: checked.CheckedProcedureTemplate, body: CheckedExprId },
        /// A builtin of the module being read: the name it answers to, and
        /// its definition.
        here_builtin: struct { name: []const u8, template: checked.CheckedProcedureTemplate, body: CheckedExprId },
        away: ForeignDefinition,
        /// A builtin: the name it answers to, and its definition, which a
        /// first stage walks.
        provided: struct { name: []const u8, definition: ForeignDefinition },

        fn template(self: MethodDefinition) checked.CheckedProcedureTemplate {
            return switch (self) {
                .here => |local| local.template,
                .here_builtin => |builtin| builtin.template,
                .away => |definition| definition.template,
                .provided => |builtin| builtin.definition.template,
            };
        }

        fn body(self: MethodDefinition) CheckedExprId {
            return switch (self) {
                .here => |local| local.body,
                .here_builtin => |builtin| builtin.body,
                .away => |definition| definition.body,
                .provided => |builtin| builtin.definition.body,
            };
        }
    };

    /// The template and body one method target names, the name a builtin
    /// answers to, or null when the walk stops there: a module it cannot read
    /// has no body and no export name to read one from.
    fn methodDefinition(self: *Reifier, template_ref: canonical.ProcedureTemplateRef, def_idx: CIR.Def.Idx) ?MethodDefinition {
        if (std.meta.eql(template_ref.artifact.bytes, self.artifact.bytes)) {
            const templates = self.procedure_templates.templates.items;
            const raw = @backingInt(template_ref.template);
            if (raw >= templates.len) return null;
            const template = templates[raw];
            const body_id = switch (template.body) {
                .checked_body => |body| body,
                .intrinsic_wrapper, .entry_wrapper, .unimplemented => return null,
            };
            const body = self.bodies.body(body_id).root_expr;
            if (self.env.module_role == .builtin) {
                return .{ .here_builtin = .{ .name = (providedName(self.names, template) orelse return null).text, .template = template, .body = body } };
            }
            return .{ .here = .{ .template = template, .body = body } };
        }
        const definition = self.walk.foreign.findExported(template_ref.artifact, def_idx) orelse return null;
        if (definition.module.env.module_role == .builtin) {
            return .{ .provided = .{
                .name = (providedName(definition.module.sources.names, definition.template) orelse return null).text,
                .definition = definition,
            } };
        }
        return .{ .away = definition };
    }

    /// What this dispatch fixes the method's quantified variables to, or null
    /// when the method has none. The edge records one type per variable in
    /// the scheme's own order.
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
    /// null when the method has none: the method's first parameter matched
    /// against the receiver's type, with every variable bound or a report.
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
    /// and hashing have recipes the normal form spells out; a codec's has to
    /// agree with its format rather than with Roc, so it stays a `Derived`
    /// the stage expands.
    fn structuralDispatch(
        self: *Reifier,
        plan: static_dispatch.StaticDispatchCallPlan,
        derivation: static_dispatch.StructuralDerivation,
        result_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        const ids = try self.dispatchExprs(plan, region);
        defer self.gpa.free(ids);
        switch (derivation) {
            .equality => {
                if (ids.len != 2) return self.rejectError(.unsupported_expression, region, "a derived equality of this arity");
                const lhs = try self.exprRef(ids[0]);
                const rhs = try self.exprRef(ids[1]);
                return self.eqOver(lhs, rhs, self.bodies.expr(ids[0]).ty, region);
            },
            .hash => {
                if (ids.len != 2) return self.rejectError(.unsupported_expression, region, "a derived hash of this arity");
                return self.hashExpr(ids[0], ids[1], result_ty, region);
            },
            .parser, .encoder, .map, .map_effectful => {
                const args = try self.exprRefs(ids);
                defer self.gpa.free(args);
                return self.derivedOf(self.names.methodNameText(plan.method), plan.dispatcher_ty, args, result_ty, region);
            },
        }
    }

    /// The evidence `entries`, recorded in this module, supply where the walk
    /// holds `scope`. An entry that forwards to an evidence param of the
    /// definition being walked is answered by the entry the call that
    /// instantiated the definition supplied, as Monotype reads a forwarded
    /// requirement off its lexical evidence chain, so a generic definition
    /// that calls another hands it what its own caller discharged.
    fn supply(self: *Reifier, entries: []const static_dispatch.CheckedEvidence, scope: SuppliedEvidence) Allocator.Error!SuppliedEvidence {
        const supplied = try self.walk.site.?.evidence.allocator().alloc(SuppliedEntry, entries.len);
        for (entries, supplied) |entry, *slot| slot.* = self.suppliedEntry(entry, scope);
        return .{ .reader = self, .entries = supplied };
    }

    /// One entry of `supply`. A forwarded entry the walk's evidence does not
    /// answer stays as recorded, so the dispatch it reaches names no target.
    fn suppliedEntry(self: *Reifier, evidence: static_dispatch.CheckedEvidence, scope: SuppliedEvidence) SuppliedEntry {
        const recorded: SuppliedEntry = .{ .reader = self, .evidence = evidence, .scope = scope };
        const forwarded = switch (evidence.resolution) {
            .constraint => |constraint| constraint,
            .direct, .structural, .from_callable, .from_scheme, .checked_error, .unreachable_value => return recorded,
        };
        if (forwarded.index.depth != 0) return recorded;
        if (forwarded.index.index >= scope.entries.len) return recorded;
        const found = scope.entries[forwarded.index.index];
        // The use's own contract for the slot, where the slot carries
        // per-use contracts, is recorded beside the slot's evidence.
        if (forwarded.callable_contract) |contract| {
            const contracts = found.evidence.callable_contracts;
            if (contracts.len != 0) {
                std.debug.assert(contract < contracts.len);
                const recorded_contract = found.reader.plans.evidence_refs[contracts.start + contract];
                return found.reader.suppliedEntry(recorded_contract, found.scope);
            }
        }
        // An independent callable relation rebuilds the target's nested
        // evidence from this use's own callable, which no table records for
        // the walk to read.
        if (forwarded.independent_callable) return recorded;
        return found;
    }

    /// The compiler-derived implementation the instantiating call supplied for
    /// one forwarded obligation, or null when it supplied a Roc body instead.
    fn forwardedDerivation(self: *Reifier, chain: static_dispatch.EvidenceChainIndex) ?static_dispatch.StructuralDerivation {
        if (chain.depth != 0) return null;
        if (chain.index >= self.evidence.entries.len) return null;
        return switch (self.evidence.entries[chain.index].evidence.resolution) {
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

    /// The name of the nominal a type is, through an alias and through what
    /// the instantiation fixed a variable to.
    fn typeName(self: *Reifier, type_id: CheckedTypeId) ?[]const u8 {
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

    // Derivations //

    /// A derived `==` on the operand type `type_id` (N1k): `is_eq` of a
    /// scalar builtin, `And` over the components of a record or tuple, nested
    /// switches over a tag union, and a nominal's own `is_eq` where it writes
    /// one.
    fn eqOver(self: *Reifier, lhs: Ref, rhs: Ref, type_id: CheckedTypeId, region: base.Region) Error!Ref {
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.eqOver(lhs, rhs, resolved.id, region);
        const b = self.bld();
        return switch (self.types.payload(resolved.id)) {
            .alias => |alias| self.eqOver(lhs, rhs, alias.backing, region),
            .nominal => |nominal| self.nominalEq(lhs, rhs, nominal, resolved.id, region),
            .record => |record| blk: {
                var fields = std.ArrayList(FieldRef).empty;
                defer fields.deinit(self.gpa);
                try self.collectRecordFields(&fields, record.fields, record.ext, region);
                const l = try self.readable(lhs);
                const r = try self.readable(rhs);
                var parts = std.ArrayList(EqPart).empty;
                defer parts.deinit(self.gpa);
                for (fields.items) |field| {
                    const name = field.reader.names.recordFieldLabelText(field.field.name);
                    try parts.append(self.gpa, .{
                        .lhs = try b.field(l, try self.fieldIndex(l, name, region)),
                        .rhs = try b.field(r, try self.fieldIndex(r, name, region)),
                        .ty = .{ .reader = field.reader, .id = field.field.ty },
                    });
                }
                break :blk try self.conjunction(parts.items, region);
            },
            .tuple => |elements| blk: {
                const l = try self.readable(lhs);
                const r = try self.readable(rhs);
                var parts = std.ArrayList(EqPart).empty;
                defer parts.deinit(self.gpa);
                for (elements, 0..) |element, k| try parts.append(self.gpa, .{
                    .lhs = try b.index(l, @intCast(k)),
                    .rhs = try b.index(r, @intCast(k)),
                    .ty = .{ .reader = self, .id = element },
                });
                break :blk try self.conjunction(parts.items, region);
            },
            .tag_union => |tag_union| self.tagUnionEq(lhs, rhs, tag_union, resolved.id, region),
            // One inhabitant, so both operands hold it.
            .empty_record => b.litBool(true),
            // No inhabitant, so no pair of values reaches the comparison: the
            // compiler derives it over no variants, and it is left to the
            // stage, as every derivation the walk does not expand is.
            .empty_tag_union => self.derivedEq(lhs, rhs, resolved.id, region),
            .flex, .rigid => |variable| blk: {
                const sealed = try self.sealedVariable(resolved.id, variable, region) orelse break :blk self.rejectOpen(type_id, region);
                break :blk b.primOf(try b.namedPrim(primitiveOwnerText(defaultBuiltin(sealed)).?, "is_eq"), &.{ lhs, rhs }, try self.rt().boolTy());
            },
            .pending, .err => self.rejectError(.unresolved_type, region, "an unresolved type"),
            .function => self.rejectError(.unsupported_type, region, "derived equality on a function"),
        };
    }

    /// Two components a derived `==` compares, and their checked type.
    const EqPart = struct { lhs: Ref, rhs: Ref, ty: TypeRef };

    /// `And` over the comparisons of `parts`, each after the first built in
    /// an operand region, so it runs only where the ones before it held.
    fn conjunction(self: *Reifier, parts: []const EqPart, region: base.Region) Error!Ref {
        const b = self.bld();
        if (parts.len == 0) return b.litBool(true);
        const first = try parts[0].ty.reader.eqOver(parts[0].lhs, parts[0].rhs, parts[0].ty.id, region);
        if (parts.len == 1) return first;
        const operands = try self.gpa.alloc(RegionId, parts.len - 1);
        defer self.gpa.free(operands);
        var earlier = std.ArrayList(Ref).empty;
        defer earlier.deinit(self.gpa);
        try earlier.append(self.gpa, first);
        for (parts[1..], operands) |part, *operand| {
            operand.* = try b.openOperand(earlier.items, .and_);
            const compare = part.ty.reader.eqOver(part.lhs, part.rhs, part.ty.id, region) catch |err| switch (err) {
                error.Diverged => invariant("a derived equality diverged"),
                error.Rejected, error.OutOfMemory => |e| return e,
            };
            try b.close(.{ .value = &.{compare} });
        }
        return b.andOf(first, operands);
    }

    /// A derived `==` over a tag union: a switch on the left operand, and in
    /// each arm a switch on the right one whose matching arm compares the
    /// payloads and whose other arms are `False`.
    fn tagUnionEq(self: *Reifier, lhs: Ref, rhs: Ref, tag_union: checked.CheckedTagUnionType, subject_id: CheckedTypeId, region: base.Region) Error!Ref {
        var variants = std.ArrayList(checked.CheckedTag).empty;
        defer variants.deinit(self.gpa);
        try self.collectVariants(&variants, tag_union.tags, tag_union.ext, region);
        if (variants.items.len == 0) return self.derivedEq(lhs, rhs, subject_id, region);
        // Each variant's name as the type table interns it, so a tag of an
        // operand finds its variant by name.
        const variant_names = try self.gpa.alloc(NameId, variants.items.len);
        defer self.gpa.free(variant_names);
        for (variants.items, variant_names) |variant, *name| name.* = try self.rt().name(self.names.tagLabelText(variant.name));
        const tags: Variants = .{ .checked = variants.items, .names = variant_names };
        const b = self.bld();
        const l = try self.readable(lhs);
        const r = try self.readable(rhs);
        const bool_ty = try self.rt().boolTy();
        const l_names = try self.memberNames(self.irs().refTy(b.row, l), region);
        defer self.gpa.free(l_names);
        const r_names = try self.memberNames(self.irs().refTy(b.row, r), region);
        defer self.gpa.free(r_names);
        if (l_names.len == 1) return self.tagEqRight(l, r, l_names[0], r_names, tags, bool_ty, region);
        const left_arms = try self.gpa.alloc(RegionId, l_names.len);
        defer self.gpa.free(left_arms);
        for (left_arms, l_names) |*left_arm, l_name| {
            left_arm.* = try b.openTagArm(l, l_name);
            try b.close(.{ .value = &.{try self.tagEqRight(l, r, l_name, r_names, tags, bool_ty, region)} });
        }
        return b.switchOn(l, left_arms, &.{}, &.{bool_ty}, &.{});
    }

    /// The inner switch of `tagUnionEq`, on the right operand, under the arm
    /// that found the left operand to be `l_name`.
    fn tagEqRight(self: *Reifier, l: Ref, r: Ref, l_name: NameId, r_names: []const NameId, tags: Variants, bool_ty: TyId, region: base.Region) Error!Ref {
        const b = self.bld();
        if (r_names.len == 1) return self.tagPairEq(l, r, l_name, r_names[0], tags, region);
        const right_arms = try self.gpa.alloc(RegionId, r_names.len);
        defer self.gpa.free(right_arms);
        for (right_arms, r_names) |*right_arm, r_name| {
            right_arm.* = try b.openTagArm(r, r_name);
            try b.close(.{ .value = &.{try self.tagPairEq(l, r, l_name, r_name, tags, region)} });
        }
        return b.switchOn(r, right_arms, &.{}, &.{bool_ty}, &.{});
    }

    /// Two tags are equal where they have one name and equal payloads.
    fn tagPairEq(self: *Reifier, l: Ref, r: Ref, l_name: NameId, r_name: NameId, tags: Variants, region: base.Region) Error!Ref {
        if (l_name != r_name) return self.bld().litBool(false);
        // An operand's union conforms to the checked one, so it has no tag
        // the checked union lacks.
        for (tags.names, tags.checked) |name, variant| {
            if (name == l_name) return self.variantEq(l, r, l_name, variant, region);
        }
        invariant("an operand of a derived equality has a tag its checked union lacks");
    }

    /// The variants of a checked tag union with their interned names.
    const Variants = struct {
        checked: []const checked.CheckedTag,
        names: []const NameId,
    };

    /// Whether the payloads of one variant agree, under the arms that found
    /// both operands to be it.
    fn variantEq(self: *Reifier, l: Ref, r: Ref, name: NameId, variant: checked.CheckedTag, region: base.Region) Error!Ref {
        const b = self.bld();
        const args = variant.argsSlice(self.types);
        const parts = try self.gpa.alloc(EqPart, args.len);
        defer self.gpa.free(parts);
        for (args, parts, 0..) |arg, *part, k| part.* = .{
            .lhs = try b.payload(l, name, @intCast(k)),
            .rhs = try b.payload(r, name, @intCast(k)),
            .ty = .{ .reader = self, .id = arg },
        };
        return self.conjunction(parts, region);
    }

    /// `==` on a nominal: `is_eq` of a scalar builtin, the nominal's own
    /// `is_eq` where it writes one, and otherwise its backing's.
    fn nominalEq(self: *Reifier, lhs: Ref, rhs: Ref, nominal: checked.CheckedNominalType, type_id: CheckedTypeId, region: base.Region) Error!Ref {
        const b = self.bld();
        if (nominal.builtin) |builtin_nominal| {
            if (isScalarEq(builtin_nominal)) {
                const owner = primitiveOwnerText(builtin_nominal).?;
                return b.primOf(try b.namedPrim(owner, "is_eq"), &.{ lhs, rhs }, try self.rt().boolTy());
            }
        }
        switch (try self.nominalMethod("is_eq", nominal, type_id, &.{ lhs, rhs }, try self.rt().boolTy(), region)) {
            .written => |call| return call,
            .derived => {},
            // The checker refuses `==` on a type that declares no equality, so
            // reaching here means the declaring module is out of the walk's
            // reach and the backing would be a guess.
            .undeclared => return self.rejectError(.unsupported_type, region, self.names.typeNameText(nominal.name)),
        }
        if (nominal.builtin != null) return self.rejectError(.unsupported_type, region, "derived equality on this builtin type");
        // An opaque type's `Ty` names it without its backing, and the
        // derivation is that backing's comparison, so expanding it here would
        // describe a representation the description hides everywhere else.
        // The stage gets the derivation, as `to_hash` through one does.
        if (nominal.is_opaque) return self.derivedEq(lhs, rhs, type_id, region);
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.rejectError(.unsupported_type, region, self.names.typeNameText(nominal.name));
        var bound_args = try self.bindNominalArgs(nominal);
        defer self.releaseNominalArgs(&bound_args);
        return self.eqOver(try self.unwrapOnce(lhs), try self.unwrapOnce(rhs), backing, region);
    }

    /// A derived `is_eq` left for the stage to expand: `Derived` over the
    /// two operands, of the type they share.
    fn derivedEq(self: *Reifier, lhs: Ref, rhs: Ref, subject_id: CheckedTypeId, region: base.Region) Error!Ref {
        const subject = try self.tyOf(subject_id, region);
        return self.bld().derived("is_eq", subject, &.{ lhs, rhs }, try self.rt().boolTy());
    }

    /// What a nominal's declaration says about one method.
    const NominalMethod = union(enum) {
        /// The method is written, and this is the call the derivation makes.
        written: Ref,
        /// The compiler derives it, so the value is its backing's.
        derived,
        /// No module in reach declares it.
        undeclared,
    };

    /// The call a nominal's own `is_eq` or `to_hash` takes, when it writes
    /// one. The method registries say which: a procedure target names a
    /// written body, and a structural target is the recipe.
    fn nominalMethod(
        self: *Reifier,
        method: []const u8,
        nominal: checked.CheckedNominalType,
        receiver: CheckedTypeId,
        args: []const Ref,
        result: TyId,
        region: base.Region,
    ) Error!NominalMethod {
        const target = self.walk.foreign.findMethod(self.foreignNominal(nominal), method) orelse return .undeclared;
        if (std.meta.activeTag(target.kind) == .structural) return .derived;
        return .{ .written = try self.writtenMethodCall(method, receiver, target, args, result, region) };
    }

    /// A nominal named the way the registries of any module can read it.
    fn foreignNominal(self: *Reifier, nominal: checked.CheckedNominalType) ForeignNominal {
        return .{
            .module = self.names.moduleIdentityBytes(nominal.origin_module),
            .source_decl = nominal.source_decl,
            .builtin = builtinMethodOwner(nominal.builtin),
        };
    }

    /// The call to a method a nominal writes, fixed by the receiver's type.
    fn writtenMethodCall(
        self: *Reifier,
        method: []const u8,
        receiver: CheckedTypeId,
        target: static_dispatch.MethodTarget,
        args: []const Ref,
        result: TyId,
        region: base.Region,
    ) Error!Ref {
        const b = self.bld();
        const fixing: MethodFixing = .{ .receiver = self.resolvedType(receiver) };
        return switch (try self.methodTargetCallee(self, target, fixing, method, receiver, region)) {
            .definition => |found| blk: {
                const row = try self.calledRow(found);
                break :blk try b.callRow(row, args);
            },
            .provided => |provided| blk: {
                const name = prims.namedOfExport(provided.name) orelse
                    break :blk self.rejectError(.unresolved_reference, region, "a builtin with no owner in its name");
                break :blk try b.primOf(try b.namedPrimWithRole(name.owner, name.method, provided.role), args, result);
            },
            .foreign => |name| try b.primOf(try b.namedPrim(name.owner, name.method), args, result),
            .none => self.rejectError(.unresolved_reference, region, "a method its nominal names no target for"),
        };
    }

    /// A derived `to_hash`: each leaf fed to the hasher by the writer's
    /// `write_*` method, in the compiler's component order. Where the walk
    /// cannot expand the recipe, the node is a `Derived` the stage refuses
    /// or expands, because only the compiler's order and widths agree with
    /// the Roc side feeding the same keys.
    fn hashExpr(self: *Reifier, value_id: CheckedExprId, hasher_id: CheckedExprId, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const value_ty = self.bodies.expr(value_id).ty;
        const hasher_ty = self.bodies.expr(hasher_id).ty;
        const value = try self.exprRef(value_id);
        const hasher = try self.exprRef(hasher_id);
        const hasher_name = self.typeName(hasher_ty) orelse
            return self.rejectError(.unresolved_type, region, "the hasher this derivation threads");
        // A builtin hasher's methods are owned by its name without the
        // module, the way every builtin `Prim` is.
        const writer = prims.ownerOfTypeName(hasher_name);
        const hasher_rty = try self.tyOf(hasher_ty, region);
        if (try self.hashOver(value, hasher, value_ty, writer, hasher_rty, region)) |hashed| return hashed;
        return self.derivedOf("to_hash", value_ty, &.{ value, hasher }, result_ty, region);
    }

    fn hashOver(self: *Reifier, value: Ref, acc: Ref, type_id: CheckedTypeId, writer: []const u8, hasher_ty: TyId, region: base.Region) Error!?Ref {
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.hashOver(value, acc, resolved.id, writer, hasher_ty, region);
        const b = self.bld();
        switch (self.types.payload(resolved.id)) {
            .alias => |alias| return self.hashOver(value, acc, alias.backing, writer, hasher_ty, region),
            .nominal => |nominal| {
                if (nominal.builtin) |builtin_nominal| {
                    const width = hasherWriteName(builtin_nominal) orelse return null;
                    return try b.primOf(try b.namedPrim(writer, width), &.{ acc, value }, hasher_ty);
                }
                switch (try self.nominalMethod("to_hash", nominal, resolved.id, &.{ value, acc }, hasher_ty, region)) {
                    .written => |call| return call,
                    .derived => {},
                    .undeclared => return null,
                }
                if (nominal.is_opaque) return null;
                const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse return null;
                var bound_args = try self.bindNominalArgs(nominal);
                defer self.releaseNominalArgs(&bound_args);
                return self.hashOver(try self.unwrapOnce(value), acc, backing, writer, hasher_ty, region);
            },
            .record => |record| {
                var fields = std.ArrayList(FieldRef).empty;
                defer fields.deinit(self.gpa);
                try self.collectRecordFields(&fields, record.fields, record.ext, region);
                const subject = try self.readable(value);
                var threaded = acc;
                for (fields.items) |field| {
                    const name = field.reader.names.recordFieldLabelText(field.field.name);
                    const component = try b.field(subject, try self.fieldIndex(subject, name, region));
                    threaded = try field.reader.hashOver(component, threaded, field.field.ty, writer, hasher_ty, region) orelse return null;
                }
                return threaded;
            },
            .tuple => |elements| {
                const subject = try self.readable(value);
                var threaded = acc;
                for (elements, 0..) |element, k| {
                    threaded = try self.hashOver(try b.index(subject, @intCast(k)), threaded, element, writer, hasher_ty, region) orelse return null;
                }
                return threaded;
            },
            // Nothing to feed the hasher, so the accumulator passes through.
            .empty_record => return acc,
            .flex, .rigid, .pending, .err, .function, .tag_union, .empty_tag_union => return null,
        }
    }

    /// A compiler-derived method left for the stage to expand: `Derived`
    /// naming the method and the type it derives for.
    fn derivedOf(self: *Reifier, method: []const u8, subject_ty: CheckedTypeId, args: []const Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const subject = try self.tyOf(subject_ty, region);
        return self.bld().derived(method, subject, args, try self.tyOf(result_ty, region));
    }

    /// `Str.inspect(value)`: the subject's own `to_inspect` when that method
    /// is the inspect override, and otherwise a `Derived` for the stage.
    fn inspectExpr(self: *Reifier, operand: CheckedExprId, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const value_ty = self.bodies.expr(operand).ty;
        const value = try self.exprRef(operand);
        var subject_ty = value_ty;
        while (true) switch (self.types.payload(subject_ty)) {
            .alias => |alias| subject_ty = alias.backing,
            .nominal => |nominal| {
                const target = self.walk.foreign.findInspectOverride(self.foreignNominal(nominal)) orelse break;
                return self.writtenMethodCall("to_inspect", subject_ty, target, &.{value}, try self.tyOf(result_ty, region), region);
            },
            .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => break,
        };
        return self.derivedOf("to_inspect", value_ty, &.{value}, result_ty, region);
    }

    /// The intrinsic the checker recorded for a call's callee, when the callee
    /// is a procedure the compiler implements.
    fn calleeIntrinsic(self: *Reifier, func: CheckedExprId) ?checked.IntrinsicId {
        const resolved = switch (self.bodies.expr(func).data) {
            .lookup_external, .lookup_required => |reference| reference orelse return null,
            .lookup_local => |local| local.resolved orelse return null,
            .pending, .numeral, .str_from_quote, .code_from_lambda, .str_segment, .str, .row_coerce, .bytes_literal, .list, .empty_list, .tuple, .match_, .if_, .call, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .unary_not, .field_access, .dispatch_call, .interpolation, .structural_eq, .structural_hash, .method_eq, .type_dispatch_call, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => return null,
        };
        return switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc => |use| use.intrinsic,
            .local_param, .local_value, .local_mutable_version, .pattern_binder, .local_proc, .selected_hoisted_const, .top_level_const, .imported_const, .hosted_proc, .platform_required_declaration, .platform_required_checked_error, .platform_required_const, .platform_required_proc, .promoted_top_level_proc => null,
        };
    }

    /// One node for a derived codec that was constructed and then run: the
    /// constructor's arguments first, the applied ones after, as one
    /// `Derived`. Null when the callee is not a derived codec.
    fn foldedCodecExpr(self: *Reifier, func: CheckedExprId, operands: []const CheckedExprId, result_ty: CheckedTypeId, region: base.Region) Error!?Ref {
        const plan_id = self.codecCallee(func) orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const constructed = try self.dispatchExprs(plan, region);
        defer self.gpa.free(constructed);
        const args = try self.gpa.alloc(Ref, constructed.len + operands.len);
        defer self.gpa.free(args);
        for (constructed, args[0..constructed.len]) |child, *arg| arg.* = try self.exprRef(child);
        for (operands, args[constructed.len..]) |child, *arg| arg.* = try self.exprRef(child);
        return try self.derivedOf(self.names.methodNameText(plan.method), plan.dispatcher_ty, args, result_ty, region);
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
                .value, .constant, .callee => null,
            };
        }
        return self.derivedCodecPlan(func);
    }

    /// The plan behind a derived parser or encoder construction, when the
    /// expression is one.
    fn derivedCodecPlan(self: *Reifier, expr_id: CheckedExprId) ?static_dispatch.StaticDispatchPlanId {
        const data = self.bodies.expr(expr_id).data;
        const dispatched = switch (data) {
            .dispatch_call => |plan_id| plan_id,
            .type_dispatch_call => |plan_id| plan_id,
            .pending, .numeral, .str_from_quote, .code_from_lambda, .str_segment, .str, .row_coerce, .bytes_literal, .lookup_local, .lookup_external, .lookup_required, .list, .empty_list, .tuple, .match_, .if_, .call, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .unary_not, .field_access, .interpolation, .structural_eq, .structural_hash, .method_eq, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => return null,
        };
        const plan_id = dispatched orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const derivation = switch (plan.resolution) {
            .structural => |structural| structural,
            .evidence_dependent => |forwarded| self.forwardedDerivation(forwarded.index) orelse return null,
            .direct_pending, .direct_closed, .direct_parametric, .checked_error, .@"unreachable" => return null,
        };
        return switch (derivation) {
            .parser, .encoder => plan_id,
            // Equality and hashing run where they are written, and a derived
            // `map` takes its function as an argument, so none is curried.
            .equality, .hash, .map, .map_effectful => null,
        };
    }

    /// Whether an expression is a call that hands back a function, which a
    /// block holds rather than binds: the call that runs it folds both
    /// halves into one.
    fn constructsFunction(self: *Reifier, expr_id: CheckedExprId) bool {
        const expr_data = self.bodies.expr(expr_id);
        const calls = switch (expr_data.data) {
            .call, .dispatch_call, .type_dispatch_call => true,
            .pending, .numeral, .str_from_quote, .code_from_lambda, .str_segment, .str, .row_coerce, .bytes_literal, .lookup_local, .lookup_external, .lookup_required, .list, .empty_list, .tuple, .match_, .if_, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .unary_not, .field_access, .interpolation, .structural_eq, .structural_hash, .method_eq, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => false,
        };
        return calls and self.functionOf(expr_data.ty) != null;
    }

    // Types //

    /// The site's type for one checked type (N1b). A builtin scalar, `Str`
    /// and `List` are the normal form's own; `Bool` is `Bool`; a nominal is
    /// `Nominal(name, backing)`, and a reference back to a nominal the walk
    /// is inside is `Recursive(name)`; a builtin the normal form has no shape
    /// for, and an opaque nominal, is `Opaque(name, args)`.
    fn tyOf(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        // Resolving at the leaf is enough: a composite holding a variable is
        // reached by recursion into the variable itself.
        if (self.fixedType(type_id)) |fixed| {
            self.substitution_uses += 1;
            const outer_through = self.walk.through;
            if (outer_through == null) self.walk.through = .{ .reader = self, .id = type_id };
            defer self.walk.through = outer_through;
            return fixed.reader.tyOf(fixed.id, region);
        }
        if (self.ty_cache.get(type_id)) |cached| return cached;
        const frame = TypeFrame{ .instance = self.nominal_instance, .id = type_id };
        if (self.type_in_progress.contains(frame)) {
            return self.rejectError(.unsupported_type, region, "a recursive type");
        }
        try self.type_in_progress.put(self.gpa, frame, {});
        defer _ = self.type_in_progress.remove(frame);

        const open_before = self.open_recursions.count();
        const uses_before = self.substitution_uses;
        const ty = try self.buildTy(type_id, region);
        // Cache only a type that stands alone: one still holding an open
        // `Recursive` means something else outside the nominal it was built
        // under, and one a substitution answered inside means something else
        // at the next instantiation.
        if (self.open_recursions.count() == open_before and self.substitution_uses == uses_before) {
            try self.ty_cache.put(self.gpa, type_id, ty);
        }
        return ty;
    }

    fn buildTy(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        const types = self.rt();
        const payload = self.types.payload(type_id);
        return switch (payload) {
            .alias => |alias| self.tyOf(alias.backing, region),
            .flex, .rigid => |variable| blk: {
                if (try self.sealedVariable(type_id, variable, region)) |target| break :blk switch (target) {
                    .dec => types.decTy(),
                    .str => types.strTy(),
                };
                // A row variable nothing pins is the row default lowering
                // seals it to (design.md "Row Coercion Primitive": a value
                // keeps its own row, so a tag built before its widening holds
                // the variable in its own type).
                if (payload == .flex and payload.variableSealsToRowDefault()) break :blk switch (variable.row_default.?) {
                    .empty_record => types.recordTy(&.{}),
                    .empty_tag_union => types.tagUnionTy(&.{}),
                };
                break :blk self.rejectOpen(type_id, region);
            },
            .pending, .err => self.rejectError(.unresolved_type, region, "an unresolved type"),
            .empty_record => types.recordTy(&.{}),
            .record => |record| self.recordTy(record.fields, record.ext, region),
            .tuple => |elements| blk: {
                const tys = try self.tysOf(elements, region);
                defer self.gpa.free(tys);
                break :blk try types.tupleTy(tys);
            },
            .function => |function| blk: {
                if (function.kind == .effectful) break :blk self.rejectError(.effect, region, "an effectful function");
                const params = try self.tysOf(function.args, region);
                defer self.gpa.free(params);
                break :blk try types.funcTy(params, try self.tyOf(function.ret, region));
            },
            .nominal => |nominal| self.nominalTy(type_id, nominal, region),
            .tag_union => |tag_union| self.tagUnionTy(tag_union.tags, tag_union.ext, region),
            .empty_tag_union => types.tagUnionTy(&.{}),
        };
    }

    fn tysOf(self: *Reifier, ids: []const CheckedTypeId, region: base.Region) Error![]TyId {
        const tys = try self.gpa.alloc(TyId, ids.len);
        errdefer self.gpa.free(tys);
        for (ids, tys) |id, *ty| ty.* = try self.tyOf(id, region);
        return tys;
    }

    /// A tag union's variants, following its extension.
    fn tagUnionTy(self: *Reifier, tags: []const checked.CheckedTag, ext: CheckedTypeId, region: base.Region) Error!TyId {
        var collected = std.ArrayList(checked.CheckedTag).empty;
        defer collected.deinit(self.gpa);
        try self.collectVariants(&collected, tags, ext, region);
        const specs = try self.gpa.alloc(reify.types.TagSpec, collected.items.len);
        defer self.gpa.free(specs);
        var filled: usize = 0;
        defer for (specs[0..filled]) |spec| self.gpa.free(spec.payload);
        for (collected.items, specs) |checked_tag, *spec| {
            spec.* = .{ .name = self.names.tagLabelText(checked_tag.name), .payload = try self.tysOf(checked_tag.argsSlice(self.types), region) };
            filled += 1;
        }
        return self.rt().tagUnionTy(specs);
    }

    /// Every variant of a tag union, following its extension.
    ///
    /// An extension that is a variable ends it, sealed to the empty union the
    /// way Monotype seals a row (`lowerCheckedTypeVariable`): a variable the
    /// checker closed carries the default that says so, and one nothing closed
    /// stands for the variants the definition names and no others. A
    /// description is monomorphic, so the variants it names are the variants
    /// it has.
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
                .flex, .rigid => break,
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

    fn nominalTy(self: *Reifier, type_id: CheckedTypeId, nominal: checked.CheckedNominalType, region: base.Region) Error!TyId {
        const types = self.rt();
        if (nominal.builtin) |builtin_nominal| {
            switch (builtin_nominal) {
                .bool => return types.boolTy(),
                .str => return types.strTy(),
                .dec => return types.decTy(),
                .f32 => return types.floatTy(.f32),
                .f64 => return types.floatTy(.f64),
                .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => return types.intTy(intTyOf(builtin_nominal).?),
                .list => {
                    if (nominal.args.len != 1) return self.rejectError(.unsupported_type, region, "List");
                    return types.listTy(try self.tyOf(nominal.args[0], region));
                },
                // `Try` is a tag union a body builds and matches, so it keeps
                // its backing.
                .try_ => {},
                .u8x16,
                .i8x16,
                .u16x8,
                .i16x8,
                .u32x4,
                .i32x4,
                .u64x2,
                .i64x2,
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
                => return self.opaqueTy(nominal, region),
            }
        }
        // An opaque nominal forbids reading its backing from outside its own
        // module, and a stage is always outside it.
        if (nominal.is_opaque) return self.opaqueTy(nominal, region);
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.opaqueTy(nominal, region);
        const name = self.names.typeNameText(nominal.name);

        // The backing is the declaration's template, written in the nominal's
        // own variables, and `args` is what this use fixed them to.
        var bound_args = try self.bindNominalArgs(nominal);
        defer self.releaseNominalArgs(&bound_args);

        // The backing is where a nominal reaches itself, and the nominal this
        // builds is what such a reference names, so open the reference before
        // descending and close it after.
        const instance = self.nominalInstanceKey(nominal);
        if (self.nominal_in_progress.get(instance)) |open| {
            try self.open_recursions.put(self.gpa, open, {});
            // What this answers depends on what the enclosing use fixed, so
            // the frame that asked declines to cache it.
            self.substitution_uses += 1;
            return types.recursiveTy(name);
        }
        try self.nominal_in_progress.put(self.gpa, instance, type_id);
        defer _ = self.nominal_in_progress.remove(instance);

        const enclosing = self.nominal_instance;
        self.nominal_instance = instance;
        defer self.nominal_instance = enclosing;

        const backing_ty = try self.tyOf(backing, region);
        _ = self.open_recursions.remove(type_id);
        return self.rt().nominalTy(name, backing_ty);
    }

    /// A key for one nominal at one instantiation: the declaration, and what
    /// this use fixed its variables to.
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
    const NominalArgs = struct {
        formals: []const CheckedTypeId = &.{},
        outer: []?TypeRef = &.{},
    };

    /// Bind a parametric nominal's declared variables to what this use fixed
    /// them to. Binds nothing when the nominal declares no variables, or when
    /// the declaration and the use disagree on how many there are.
    fn bindNominalArgs(self: *Reifier, nominal: checked.CheckedNominalType) Allocator.Error!NominalArgs {
        if (nominal.args.len == 0) return .{};
        const declaration = self.types.nominalDeclarationForPayload(nominal) orelse return .{};
        const formals = declaration.formalArgs(self.types);
        if (formals.len != nominal.args.len) return .{};
        // Every use is read before any formal is bound, so one formal's
        // binding cannot answer another's.
        const fixed = try self.gpa.alloc(TypeRef, nominal.args.len);
        defer self.gpa.free(fixed);
        for (nominal.args, fixed) |arg, *use| use.* = self.resolvedType(arg);
        const outer = try self.gpa.alloc(?TypeRef, formals.len);
        errdefer self.gpa.free(outer);
        for (formals, fixed, outer) |formal, use, *saved| {
            saved.* = self.nominal_args.get(formal);
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

    /// A nominal the normal form has no shape for, named with its type
    /// arguments.
    fn opaqueTy(self: *Reifier, nominal: checked.CheckedNominalType, region: base.Region) Error!TyId {
        const args = try self.tysOf(nominal.args, region);
        defer self.gpa.free(args);
        return self.rt().opaqueTy(self.names.typeNameText(nominal.name), args);
    }

    /// A record type's fields, following its extension. A field is optional
    /// only where the checker pinned it so; a defaulted field is filled in,
    /// and an unpinned one is what the checker commits to required.
    fn recordTy(self: *Reifier, fields: []const checked.CheckedRecordField, ext: ?CheckedTypeId, region: base.Region) Error!TyId {
        var collected = std.ArrayList(FieldRef).empty;
        defer collected.deinit(self.gpa);
        try self.collectRecordFields(&collected, fields, ext, region);
        const specs = try self.gpa.alloc(reify.types.FieldSpec, collected.items.len);
        defer self.gpa.free(specs);
        for (collected.items, specs) |field, *spec| {
            const optional = switch (field.field.kind.tag) {
                .required, .defaulted, .undetermined => false,
                .optional => true,
                .err => return self.rejectError(.unresolved_type, region, "a record field whose presence is an error"),
            };
            spec.* = .{
                .name = field.reader.names.recordFieldLabelText(field.field.name),
                .ty = try field.reader.tyOf(field.field.ty, region),
                .optional = optional,
            };
        }
        return self.rt().recordTy(specs);
    }

    /// Every field of a record type, following its extension.
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
                .flex, .rigid => |variable| {
                    const bound = reader.fixedType(next) orelse {
                        // A row variable nothing fixes is the row default
                        // lowering seals it to, as `buildTy` reads one.
                        const payload = reader.types.payload(next);
                        if (payload == .flex and payload.variableSealsToRowDefault() and variable.row_default.? == .empty_record) break;
                        return self.rejectError(.unresolved_type, region, "an open record");
                    };
                    // The fields from here on are what one site fixed, so the
                    // frame that asked declines to cache this type.
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
    /// named it.
    fn collectField(self: *Reifier, collected: *std.ArrayList(FieldRef), reader: *Reifier, field: checked.CheckedRecordField) Allocator.Error!void {
        for (collected.items) |seen| {
            if (seen.reader.sameFieldLabel(seen.field.name, reader, field.name)) return;
        }
        try collected.append(self.gpa, .{ .reader = reader, .field = field });
    }

    fn rejectError(self: *Reifier, kind: Rejection.Kind, region: base.Region, detail: []const u8) error{Rejected} {
        if (self.walk.rejection == null) {
            self.walk.rejection = .{ .kind = kind, .region = region, .detail = detail };
        }
        return error.Rejected;
    }

    /// Refuse a type variable, naming it and the place in the signature it
    /// stands in. A variable reached through a substitution is named by the
    /// quantified variable the annotation wrote, and the use left it open.
    fn rejectOpen(self: *Reifier, type_id: CheckedTypeId, region: base.Region) error{Rejected} {
        const named = self.walk.through orelse TypeRef{ .reader = self, .id = type_id };
        const variable = switch (named.reader.types.payload(named.id)) {
            .flex, .rigid => |variable| variable,
            .pending,
            .err,
            .alias,
            .record,
            .tuple,
            .nominal,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => invariant("a substitution answered for a type that is not a variable"),
        };
        // Through a use, the definition's own variable says whether an
        // annotation wrote it: an annotation names each variable, and
        // checking names none it infers. What the use put in its place says
        // only that the use left it open.
        const own = self.types.payload(type_id);
        const cause: OpenVariable.Cause = if (self.walk.through != null) switch (own) {
            .rigid => .use_leaves_open,
            .flex => |own_variable| if (own_variable.name != null) .use_leaves_open else .inferred_use_leaves_open,
            .pending, .err, .alias, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => invariant("a type variable was refused at a type that is not a variable"),
        } else if (own == .rigid)
            .annotation_leaves_open
        else
            .inferred;
        const at, const place: OpenVariable.Place = switch (self.walk.place) {
            .expression => .{ region, .expression },
            .result => .{ region, .result },
            .parameter => |param| blk: {
                const pattern = param.reader.bodies.pattern(param.pattern);
                const binder = param.reader.bodies.patternBinderForCheckedPattern(param.pattern);
                const single = binder != null and (pattern.data == .assign or pattern.data == .as);
                break :blk .{ pattern.source_region, .{ .parameter = if (single)
                    .{ .name = param.reader.binderName(binder.?) }
                else
                    .{ .position = param.position + 1 } } };
            },
        };
        if (self.walk.rejection == null) {
            self.walk.rejection = .{
                .kind = .unresolved_type,
                .region = at,
                .detail = "a type variable",
                .open = .{ .name = variable.name, .place = place, .cause = cause },
            };
        }
        return error.Rejected;
    }

    /// What a variable no substitution fixed seals to (`defaultedVariable`),
    /// null for one with no default, or a refusal for one whose default does
    /// not fit the dispatch that selected it.
    fn sealedVariable(self: *Reifier, type_id: CheckedTypeId, variable: checked.CheckedTypeVariable, region: base.Region) error{Rejected}!?checked.literal_defaulting.DefaultTarget {
        const sealed = defaultedVariable(variable) orelse return null;
        if (self.unfit.contains(type_id)) {
            return self.rejectError(.unresolved_type, region, "a type variable whose numeric default has no method that fits how it is used");
        }
        return sealed;
    }

    /// Build a signature type with the walk told where in the signature it
    /// stands, so a refusal at a type variable names the place.
    fn placedTy(self: *Reifier, type_id: CheckedTypeId, region: base.Region, place: TypePlace) Error!TyId {
        const outer = self.walk.place;
        self.walk.place = place;
        defer self.walk.place = outer;
        return self.tyOf(type_id, region);
    }

    fn functionOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedFunctionType {
        return switch (self.types.payload(type_id)) {
            .function => |function| function,
            .alias => |alias| self.functionOf(alias.backing),
            .pending, .err, .flex, .rigid, .record, .tuple, .nominal, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The nominal a checked id is, reading through an alias. Reads this
    /// reader's store alone, because the args it carries are ids of that
    /// store.
    fn nominalOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedNominalType {
        return switch (self.types.payload(type_id)) {
            .nominal => |nominal| nominal,
            .alias => |alias| self.nominalOf(alias.backing),
            .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The elements a checked id is a tuple of, reading through an alias.
    fn tupleOf(self: *Reifier, type_id: CheckedTypeId) ?[]const CheckedTypeId {
        return switch (self.types.payload(type_id)) {
            .tuple => |elements| elements,
            .alias => |alias| self.tupleOf(alias.backing),
            .pending, .err, .flex, .rigid, .record, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The builtin a checked type is, through an alias and through what the
    /// instantiation fixed a variable to.
    fn primitiveOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedBuiltinNominal {
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.primitiveOf(resolved.id);
        return switch (self.types.payload(resolved.id)) {
            .alias => |alias| self.primitiveOf(alias.backing),
            .nominal => |nominal| nominal.builtin,
            .flex, .rigid => |variable| if (self.unfit.contains(resolved.id)) null else if (defaultedVariable(variable)) |sealed| defaultBuiltin(sealed) else null,
            .pending, .err, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The builtin module a checked type's methods belong to, as `Builtin.roc`
    /// exports it, when the type is a scalar builtin.
    fn primitiveOwner(self: *Reifier, type_id: CheckedTypeId) ?[]const u8 {
        return primitiveOwnerText(self.primitiveOf(type_id) orelse return null);
    }

    /// The scalar builtin a site type is.
    fn primitiveOfTy(self: *Reifier, ty: TyId) ?checked.CheckedBuiltinNominal {
        return switch (self.rt().get(ty)) {
            .bool_ => .bool,
            .str => .str,
            .dec => .dec,
            .float => |float| switch (float) {
                .f32 => .f32,
                .f64 => .f64,
            },
            .int => |int| switch (int) {
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
            },
            .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => null,
        };
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
        use_expr: ?CheckedExprId,
        region: base.Region,
        unfixed: Unfixed,
    ) Error!?Instantiation {
        const scheme_vars = scheme.vars;
        if (scheme_vars.len == 0) return null;
        const payload = fixed orelse {
            // A use that fixes no type leaves a hole only where the scheme
            // quantifies something other than a row (`rowVars`).
            var rows = try self.rowVars(scheme.root);
            defer rows.deinit(self.gpa);
            for (scheme_vars) |scheme_var| {
                if (!rows.contains(scheme_var)) return self.rejectError(.unresolved_type, region, unfixed.missing);
            }
            return null;
        };

        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        try self.matchType(&substitution, scheme_vars, scheme.root, caller.resolvedType(payload));

        // A variable only a `where` obligation names, such as the literal's
        // in `f = |x| x * 2`, is not in `f`'s type, so the match cannot reach
        // it. The checker recorded what the use copied every variable to, and
        // the dispatch that obligation selected fixed the copy.
        if (use_expr) |expr| {
            if (caller.plans.siteSubstitution(expr)) |copied| {
                if (copied.len != scheme_vars.len) invariant("a use's recorded substitution disagrees with its scheme's variables");
                for (scheme_vars, copied) |scheme_var, copy| {
                    if (substitution.contains(scheme_var)) continue;
                    try substitution.put(self.gpa, scheme_var, caller.resolvedType(copy));
                }
            }
        }

        var rows = try self.rowVars(scheme.root);
        defer rows.deinit(self.gpa);

        // `scheme_vars` is the domain, so a variable the match left unbound is
        // a hole in the body, and a description with a hole in it is worse
        // than a report saying the use was not described. A row variable is
        // the exception, because no description names one.
        for (scheme_vars) |scheme_var| {
            if (substitution.contains(scheme_var)) continue;
            if (rows.contains(scheme_var)) continue;
            const variable = switch (self.types.payload(scheme_var)) {
                .flex, .rigid => |variable| variable,
                .pending,
                .err,
                .alias,
                .record,
                .tuple,
                .nominal,
                .function,
                .empty_record,
                .tag_union,
                .empty_tag_union,
                => invariant("a scheme quantifies over a type that is not a variable"),
            };
            if (self.walk.rejection == null) {
                self.walk.rejection = .{
                    .kind = .unresolved_type,
                    .region = region,
                    .detail = unfixed.partial,
                    .open = .{
                        .name = variable.name,
                        .place = .{ .use = unfixed.use },
                        .cause = if (self.types.payload(scheme_var) == .rigid) .use_leaves_open else .inferred,
                    },
                };
            }
            return error.Rejected;
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
            // A `where` obligation is part of the scheme, and a row its
            // method's type stands on is a row of the scheme too.
            .flex, .rigid => |variable| for (variable.constraints) |constraint| try self.collectRowVars(found, seen, constraint.fn_ty),
            .empty_record, .empty_tag_union, .pending, .err => {},
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
            // The checker lifts a structural record or tag union into a
            // nominal it meets (unify.zig `mergeToNominal`), so where the use
            // holds a nominal the scheme's structure stands for that nominal
            // at this use. The structure is no variable, so the lift is an
            // entry of its own, and the key names it (`instantiationKey`).
            .record, .tag_union => if (use.reader.nominalOf(use.id) != null) {
                if (!substitution.contains(scheme_id)) try substitution.put(self.gpa, scheme_id, use);
            } else switch (self.types.payload(scheme_id)) {
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
                .alias, .function, .nominal, .tuple, .empty_record, .empty_tag_union, .flex, .rigid, .pending, .err => unreachable, // the outer switch reached this for a record or a tag union only
            },
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
        // A structure the use lifted into a nominal (`matchType`) is keyed
        // too, by the nominal it stands for: a use that lifts it and one that
        // does not are two types the definition is called at. The structure's
        // id is canonical in the defining module, which every use shares, and
        // the entries are in the order the match met them, which the scheme
        // fixes.
        var entries = substitution.constIterator();
        while (entries.next()) |entry| {
            if (std.mem.indexOfScalar(CheckedTypeId, scheme_vars, entry.key_ptr.*) != null) continue;
            hasher.update(std.mem.asBytes(&@backingInt(entry.key_ptr.*)));
            hasher.update(&entry.value_ptr.reader.types.rootKey(entry.value_ptr.id).bytes);
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
        if (self.nominal_args.get(type_id)) |fixed| return fixed;
        return self.related.get(type_id);
    }

    /// Relate every monomorphic dispatch target that publication selected for
    /// a callable checking never instantiated to that callable, once per
    /// module.
    ///
    /// Such an edge is `derived_from_callable`: publication chose the target
    /// (the numeric default owner of a dispatcher no edge pins, the procedure
    /// an alias reaches, or a literal conversion), and the edge's contract is
    /// that specialization relates the target's type to the callable. That is
    /// what fixes `y` in `|x, y| x + y`: `x` seals to `Dec`, publication
    /// selected `Dec.plus`, and `Dec.plus : Dec, Dec -> Dec` fixes the other
    /// argument and the result. Monotype honours the contract when it lowers
    /// the dispatch, and a description is the same specialization read
    /// without lowering, so the walk honours it here. A generic target fixes
    /// none of the callable's variables by its own type, so it is not related.
    fn relateSelectedTargets(self: *Reifier) Allocator.Error!void {
        if (self.related_ready) return;
        self.related_ready = true;
        var variables = std.ArrayList(CheckedTypeId).empty;
        defer variables.deinit(self.gpa);
        var seen: RowVars = .empty;
        defer seen.deinit(self.gpa);
        for (self.plans.evidence_nodes) |node| {
            const callable = switch (node.instantiation) {
                .derived_from_callable => |callable| callable,
                .monomorphic, .callable, .alias => continue,
            };
            const procedure = switch (node.target.kind) {
                .procedure => |procedure| procedure,
                .local_proc, .structural => continue,
            };
            const target = try self.targetTemplate(procedure.template, node.target.def_idx) orelse continue;
            if (target.reader.schemeVars(target.template).len != 0) continue;
            const target_fn: TypeRef = .{ .reader = target.reader, .id = target.template.checked_fn_root };
            if (!self.fitsTarget(callable, target_fn)) {
                if (node.dispatcher_ty) |dispatcher| try self.unfit.put(self.gpa, dispatcher, {});
                continue;
            }
            variables.clearRetainingCapacity();
            seen.clearRetainingCapacity();
            try self.collectVariables(&variables, &seen, callable);
            try self.matchType(&self.related, variables.items, callable, target_fn);
        }
    }

    /// Whether a monomorphic target's type agrees with a callable everywhere
    /// the callable is not a variable, so relating the two fixes the
    /// callable's variables rather than contradicting its concrete parts.
    fn fitsTarget(self: *Reifier, callable: CheckedTypeId, target: TypeRef) bool {
        const use = target.reader.resolvedType(target.id);
        const use_payload = use.reader.types.payload(use.id);
        switch (use_payload) {
            .alias => |alias| return self.fitsTarget(callable, .{ .reader = use.reader, .id = alias.backing }),
            // The target leaves this part to the callable.
            .flex, .rigid => return true,
            .pending, .err => return false,
            .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => {},
        }
        return switch (self.types.payload(callable)) {
            .flex, .rigid => true,
            .alias => |alias| self.fitsTarget(alias.backing, use),
            .pending, .err => false,
            .empty_record => use_payload == .empty_record,
            .empty_tag_union => use_payload == .empty_tag_union,
            .function => |fn_ty| blk: {
                const use_fn = switch (use_payload) {
                    .function => |use_fn| use_fn,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .nominal, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (fn_ty.args.len != use_fn.args.len) break :blk false;
                for (fn_ty.args, use_fn.args) |arg, use_arg| {
                    if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg })) break :blk false;
                }
                break :blk self.fitsTarget(fn_ty.ret, .{ .reader = use.reader, .id = use_fn.ret });
            },
            .nominal => |nominal| blk: {
                const use_nominal = switch (use_payload) {
                    .nominal => |use_nominal| use_nominal,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                // Ids are each store's own, so this side's names are looked
                // up in the target's store.
                if (use.reader.names.lookupModuleIdentity(self.names.moduleIdentityBytes(nominal.origin_module)) != use_nominal.origin_module) break :blk false;
                if (use.reader.names.lookupTypeName(self.names.typeNameText(nominal.name)) != use_nominal.name) break :blk false;
                if (nominal.args.len != use_nominal.args.len) break :blk false;
                for (nominal.args, use_nominal.args) |arg, use_arg| {
                    if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg })) break :blk false;
                }
                break :blk true;
            },
            .tuple => |parts| blk: {
                const use_parts = switch (use_payload) {
                    .tuple => |use_parts| use_parts,
                    .pending, .err, .flex, .rigid, .alias, .record, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (parts.len != use_parts.len) break :blk false;
                for (parts, use_parts) |part, use_part| {
                    if (!self.fitsTarget(part, .{ .reader = use.reader, .id = use_part })) break :blk false;
                }
                break :blk true;
            },
            .record => |record| blk: {
                const use_record = switch (use_payload) {
                    .record => |use_record| use_record,
                    .pending, .err, .flex, .rigid, .alias, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (record.fields.len != use_record.fields.len) break :blk false;
                for (record.fields) |field| {
                    const name = use.reader.names.lookupRecordFieldLabel(self.names.recordFieldLabelText(field.name)) orelse break :blk false;
                    const match = for (use_record.fields) |use_field| {
                        if (use_field.name == name) break use_field;
                    } else break :blk false;
                    if (!self.fitsTarget(field.ty, .{ .reader = use.reader, .id = match.ty })) break :blk false;
                }
                break :blk self.fitsTarget(record.ext, .{ .reader = use.reader, .id = use_record.ext });
            },
            .tag_union => |union_ty| blk: {
                const use_union = switch (use_payload) {
                    .tag_union => |use_union| use_union,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .nominal, .function, .empty_record, .empty_tag_union => break :blk false,
                };
                if (union_ty.tags.len != use_union.tags.len) break :blk false;
                for (union_ty.tags) |variant| {
                    const name = use.reader.names.lookupTagLabel(self.names.tagLabelText(variant.name)) orelse break :blk false;
                    const match = for (use_union.tags) |use_variant| {
                        if (use_variant.name == name) break use_variant;
                    } else break :blk false;
                    const args = variant.argsSlice(self.types);
                    const use_args = match.argsSlice(use.reader.types);
                    if (args.len != use_args.len) break :blk false;
                    for (args, use_args) |arg, use_arg| {
                        if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg })) break :blk false;
                    }
                }
                break :blk self.fitsTarget(union_ty.ext, .{ .reader = use.reader, .id = use_union.ext });
            },
        };
    }

    /// The template one method target names and the reader of the module that
    /// declares it, or null for a module the walk cannot read.
    fn targetTemplate(
        self: *Reifier,
        template_ref: canonical.ProcedureTemplateRef,
        def_idx: CIR.Def.Idx,
    ) Allocator.Error!?struct { reader: *Reifier, template: checked.CheckedProcedureTemplate } {
        if (std.meta.eql(template_ref.artifact.bytes, self.artifact.bytes)) {
            const templates = self.procedure_templates.templates.items;
            const raw = @backingInt(template_ref.template);
            if (raw >= templates.len) return null;
            return .{ .reader = self, .template = templates[raw] };
        }
        const definition = self.walk.foreign.findExported(.{ .bytes = template_ref.artifact.bytes }, def_idx) orelse return null;
        return .{ .reader = try self.walk.reader(definition.module), .template = definition.template };
    }

    /// Every type variable one checked type reaches, in this reader's store.
    fn collectVariables(self: *Reifier, found: *std.ArrayList(CheckedTypeId), seen: *RowVars, id: CheckedTypeId) Allocator.Error!void {
        if ((try seen.getOrPut(self.gpa, id)).found_existing) return;
        switch (self.types.payload(id)) {
            .flex, .rigid => try found.append(self.gpa, id),
            .alias => |alias| try self.collectVariables(found, seen, alias.backing),
            .function => |fn_ty| {
                for (fn_ty.args) |arg| try self.collectVariables(found, seen, arg);
                try self.collectVariables(found, seen, fn_ty.ret);
            },
            .nominal => |nominal| for (nominal.args) |arg| try self.collectVariables(found, seen, arg),
            .tuple => |parts| for (parts) |part| try self.collectVariables(found, seen, part),
            .record => |record| {
                for (record.fields) |field| try self.collectVariables(found, seen, field.ty);
                try self.collectVariables(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                for (union_ty.tags) |variant| {
                    for (variant.argsSlice(self.types)) |arg| try self.collectVariables(found, seen, arg);
                }
                try self.collectVariables(found, seen, union_ty.ext);
            },
            .empty_record, .empty_tag_union, .pending, .err => {},
        }
    }
};

/// Where in a row's signature a type stands. The pattern of a parameter is
/// named in the module of `reader`.
const TypePlace = union(enum) {
    expression,
    parameter: struct { reader: *Reifier, pattern: CheckedPatternId, position: u32 },
    result,
};

/// The builtin a type variable stands for where nothing fixed it, or null for
/// one with no default.
///
/// The walk describes a function the way Monotype specializes one: a variable
/// a substitution fixes is read through it first (`fixedType`), and a variable
/// still open after that is sealed by the default checking published on it,
/// by the rule `lowerCheckedTypeVariable` seals it by. So `x` in `|x| x * 2`
/// describes at `Dec`, and `x` in `same = |x| x`, which carries no default,
/// stays open and is refused.
fn defaultedVariable(variable: checked.CheckedTypeVariable) ?checked.literal_defaulting.DefaultTarget {
    const phase = variable.numeric_default_phase orelse return null;
    return checked.literal_defaulting.defaultTargetForPhase(phase) orelse
        invariant("a checking-finalized numeric variable reached publication unresolved");
}

/// The builtin a default seals a variable to.
fn defaultBuiltin(target: checked.literal_defaulting.DefaultTarget) checked.CheckedBuiltinNominal {
    return switch (target) {
        .dec => .dec,
        .str => .str,
    };
}

/// Stop on a broken invariant of the walk: a state no input reaches.
fn invariant(comptime message: []const u8) noreturn {
    base.invariant("code reifier invariant: " ++ message, .{});
}

/// Where `id` first sits in `ids`.
fn positionOf(comptime Id: type, ids: []const Id, id: Id) ?usize {
    for (ids, 0..) |each, index| {
        if (each == id) return index;
    }
    return null;
}

/// Whether two modules belong to one package, by the name the workspace gives
/// each (N8h). A module no coordinator placed in a package belongs to the
/// unnamed one.
fn samePackage(a: *const ModuleEnv, b: *const ModuleEnv) bool {
    return std.mem.eql(u8, packageText(a), packageText(b));
}

fn packageText(env: *const ModuleEnv) []const u8 {
    return env.package_name;
}

/// The method an arithmetic or comparison operator desugars to.
fn binopMethod(op: CIR.Expr.Binop.Op) []const u8 {
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
        .eq, .ne => "is_eq",
        .@"and", .@"or", .range_exclusive, .range_inclusive => invariant("a connective or range reached the operator table"),
    };
}

/// The builtin module a scalar builtin's methods belong to, as `Builtin.roc`
/// exports it.
fn primitiveOwnerText(primitive: checked.CheckedBuiltinNominal) ?[]const u8 {
    return switch (primitive) {
        .bool => "Bool",
        .str => "Str",
        .u8 => "Num.U8",
        .i8 => "Num.I8",
        .u16 => "Num.U16",
        .i16 => "Num.I16",
        .u32 => "Num.U32",
        .i32 => "Num.I32",
        .u64 => "Num.U64",
        .i64 => "Num.I64",
        .u128 => "Num.U128",
        .i128 => "Num.I128",
        .f32 => "Num.F32",
        .f64 => "Num.F64",
        .dec => "Num.Dec",
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

/// The site integer type of an integer builtin.
fn intTyOf(primitive: checked.CheckedBuiltinNominal) ?reify.types.IntTy {
    const target = intTarget(primitive) orelse return null;
    return switch (target) {
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
        .f32, .f64, .dec => null,
    };
}

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

/// The numeral target of an integer builtin, or null for any other type.
fn intTarget(primitive: checked.CheckedBuiltinNominal) ?numeral.Target {
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

fn patternFormName(data: checked.CheckedPatternData) []const u8 {
    return switch (data) {
        .list => "a list pattern",
        .str_interpolation => "a string interpolation pattern",
        .runtime_error => "a pattern that failed to compile",
        .pending,
        .as,
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

/// Where a node of a site came from (N10): the module whose source holds
/// it, and its region there.
pub const Source = struct {
    module: checked.CheckedModuleArtifactKey,
    region: base.Region,
};

/// One finished site's provenance: the key its `Code` value carries, its
/// sources, and the origins of its graph's nodes as indexes into them.
pub const SiteProvenance = struct {
    key: u64,
    sources: []Source,
    origins: reify.provenance.Emitted,

    pub fn deinit(self: *SiteProvenance, gpa: Allocator) void {
        gpa.free(self.sources);
        self.origins.deinit(gpa);
    }
};

/// One staged site's result: the checked expression that carries the
/// description, and either the description or the reason the walk stopped.
pub const SiteOutcome = struct {
    expr: CheckedExprId,
    outcome: Outcome,
    /// The site's input slots, in slot order. Empty unless the site's
    /// translator returns a `Code.Bound` and the description reads a value
    /// that exists only at run time.
    slots: []SlotSource = &.{},
    /// The call that binds the site's input slots, as the checker recorded
    /// it, or null.
    bound_call: ?u32 = null,
};

/// What the program supplies for one input slot: a run-time name, read
/// through these projections at the call (N18b).
pub const SlotSource = struct {
    leaf: PatternBinderId,
    steps: []const SlotStep,
    /// The slot type's shape (`slotShape`), which the site lowering checks
    /// the value it builds against in debug builds.
    shape: []const u32,
};

/// One projection of a slot source.
pub const SlotStep = union(enum) {
    field: canonical.RecordFieldLabelId,
    index: u32,
    unwrap,
};

/// The words that say the shape of a slot of type `ty`, in pre-order, which
/// the site lowering compares with the type it builds a `Code.Value` at in
/// debug builds (`CodeValueShape` in `checked_artifact.zig` names the
/// words). Returns why the type holds a shape no `Code.Value` expresses, or
/// null.
fn slotShape(
    gpa: Allocator,
    types: *const Types,
    names: *const canonical.CanonicalNameStore,
    ty: TyId,
    out: *std.ArrayList(u32),
) Allocator.Error!?[]const u8 {
    const S = checked.CodeValueShape;
    const Item = union(enum) { ty: TyId, word: u32 };
    var pending = std.ArrayList(Item).empty;
    defer pending.deinit(gpa);
    try pending.append(gpa, .{ .ty = ty });
    while (pending.pop()) |item| {
        const current = switch (item) {
            .word => |word| {
                try out.append(gpa, word);
                continue;
            },
            .ty => |current| current,
        };
        switch (types.get(current)) {
            .func => return "a captured function value",
            .opaque_ => return "a captured value of an opaque type",
            .int => |int| try out.appendSlice(gpa, &.{ @intFromEnum(S.int), @intFromEnum(int) }),
            .float => |float| try out.appendSlice(gpa, &.{ @intFromEnum(S.frac), @intFromBool(float == .f64) }),
            .dec => try out.append(gpa, @intFromEnum(S.dec)),
            .bool_ => try out.append(gpa, @intFromEnum(S.bool_)),
            .str => try out.append(gpa, @intFromEnum(S.str)),
            .recursive => try out.append(gpa, @intFromEnum(S.recursive)),
            .list => |elem| {
                try out.append(gpa, @intFromEnum(S.list));
                try pending.append(gpa, .{ .ty = elem });
            },
            .nominal => |n| {
                try out.append(gpa, @intFromEnum(S.wrap));
                try pending.append(gpa, .{ .ty = n.backing });
            },
            .tuple => |span| {
                const items = types.tySlice(span);
                try out.appendSlice(gpa, &.{ @intFromEnum(S.tuple), @intCast(items.len) });
                var i = items.len;
                while (i > 0) {
                    i -= 1;
                    try pending.append(gpa, .{ .ty = items[i] });
                }
            },
            .record => |span| {
                const fields = types.memberSlice(span);
                try out.appendSlice(gpa, &.{ @intFromEnum(S.record), @intCast(fields.len) });
                var i = fields.len;
                while (i > 0) {
                    i -= 1;
                    const field = fields[i];
                    if (field.optional) return "a captured record with an optional field";
                    const label = names.lookupRecordFieldLabel(types.nameText(field.name)) orelse
                        invariant("a field of a slot type has no label in the site's module");
                    try pending.append(gpa, .{ .ty = types.tySlice(field.tys)[0] });
                    try pending.append(gpa, .{ .word = @backingInt(label) });
                }
            },
            .tag_union => |span| {
                const tags = types.memberSlice(span);
                try out.appendSlice(gpa, &.{ @intFromEnum(S.tag_union), @intCast(tags.len) });
                var i = tags.len;
                while (i > 0) {
                    i -= 1;
                    const tag = tags[i];
                    const label = names.lookupTagLabel(types.nameText(tag.name)) orelse
                        invariant("a tag of a slot type has no label in the site's module");
                    const payloads = types.tySlice(tag.tys);
                    var p = payloads.len;
                    while (p > 0) {
                        p -= 1;
                        try pending.append(gpa, .{ .ty = payloads[p] });
                    }
                    try pending.append(gpa, .{ .word = @intCast(payloads.len) });
                    try pending.append(gpa, .{ .word = @backingInt(label) });
                }
            },
        }
    }
    return null;
}

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

/// An exact function alias another module exports, `same = add_one`: the
/// module that holds it, and the lookup the checker recorded as the function
/// the alias names.
pub const ForeignAlias = struct {
    module: ForeignModule,
    lookup: CheckedExprId,
};

/// A top-level value another module exports that computes a function: the
/// module that holds it, and the checked expression it was written as.
pub const ForeignComputed = struct {
    module: ForeignModule,
    body: CheckedExprId,
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
    /// An exact function alias a staged site names through an import.
    resolve_alias: *const fn (
        context: *const anyopaque,
        import_idx: CIR.Import.Idx,
        target_node_idx: u32,
    ) ?ForeignAlias,
    resolve_exported: *const fn (
        context: *const anyopaque,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignDefinition,
    /// An exact function alias of a named artifact, which a call reaches the
    /// way it reaches a definition: the alias has no body of its own, so the
    /// walk follows the lookup it forwards to.
    resolve_exported_alias: *const fn (
        context: *const anyopaque,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignAlias,
    /// A top-level value of a named artifact that computes a function,
    /// `doubler = make(2.0)`: the module that holds it, and the checked
    /// expression it was written as.
    resolve_exported_computed: *const fn (
        context: *const anyopaque,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignComputed,
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
        .resolve_alias = resolveNothingImportedAlias,
        .resolve_exported = resolveNothingExported,
        .resolve_exported_alias = resolveNothingAlias,
        .resolve_exported_computed = resolveNothingComputed,
        .resolve_constant = resolveNothingConstant,
        .resolve_method = resolveNothingMethod,
        .resolve_inspect_override = resolveNothingInspectOverride,
    };

    fn resolveNothing(_: *const anyopaque, _: CIR.Import.Idx, _: u32) ?ForeignDefinition {
        return null;
    }

    fn resolveNothingImportedAlias(_: *const anyopaque, _: CIR.Import.Idx, _: u32) ?ForeignAlias {
        return null;
    }

    fn resolveNothingExported(_: *const anyopaque, _: canonical.ArtifactRef, _: CIR.Def.Idx) ?ForeignDefinition {
        return null;
    }

    fn resolveNothingAlias(_: *const anyopaque, _: canonical.ArtifactRef, _: CIR.Def.Idx) ?ForeignAlias {
        return null;
    }

    fn resolveNothingComputed(_: *const anyopaque, _: canonical.ArtifactRef, _: CIR.Def.Idx) ?ForeignComputed {
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

    fn findAlias(
        self: ForeignLookup,
        import_idx: CIR.Import.Idx,
        target_node_idx: u32,
    ) ?ForeignAlias {
        return self.resolve_alias(self.context, import_idx, target_node_idx);
    }

    fn findExported(
        self: ForeignLookup,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignDefinition {
        return self.resolve_exported(self.context, artifact, def);
    }

    fn findExportedAlias(
        self: ForeignLookup,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignAlias {
        return self.resolve_exported_alias(self.context, artifact, def);
    }

    fn findExportedComputed(
        self: ForeignLookup,
        artifact: canonical.ArtifactRef,
        def: CIR.Def.Idx,
    ) ?ForeignComputed {
        return self.resolve_exported_computed(self.context, artifact, def);
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
    /// The site being built: its IR store, type table and builder. Null
    /// between sites.
    site: ?*SiteIr = null,
    /// Every definition the site's walk has reached, and its row.
    definitions: std.AutoHashMapUnmanaged(DefinitionKey, Definition) = .empty,
    /// The rows the walk is inside, outermost first.
    rows: std.ArrayList(RowId) = .empty,
    /// How many interpolated literals' first stage the walk is inside (see
    /// `interpolationExpr`). Zero inside every row, so the rows a stage
    /// builds are ordinary rows.
    stage_one: u32 = 0,
    /// Whether the call being resolved reaches the Roc definition of a
    /// builtin, rather than naming it, which only a first stage does.
    open_builtins: bool = false,
    /// The lambdas a first stage wrote, by the row each is a closure of: what
    /// the walk applies where it stands (`appliedInline`).
    closure_targets: std.AutoHashMapUnmanaged(RowId, Reifier.CalleeTarget) = .empty,
    /// The root row of the site last emitted, which a test dumps.
    root: ?RowId = null,
    rejection: ?Rejection = null,
    /// The part of a row's signature whose type `tyOf` is building, which a
    /// refusal at a type variable names. `.expression` everywhere else.
    place: TypePlace = .expression,
    /// The quantified variable whose substitution `tyOf` is inside, the
    /// outermost one, or null outside every substitution. A variable the
    /// use left open is named by the one the annotation wrote.
    through: ?Reifier.TypeRef = null,
    /// The view the site being walked declares (plan 1.5, V6).
    view: View = .graph,
    /// Per view, digest of the rows a site's walk built, and digest of
    /// their nodes' origins: the `Graph` their normal form wrote in that
    /// view, and the origins of its nodes (P1). The walk is deterministic,
    /// so a site whose walk built the same rows from sources it met in the
    /// same order, such as a second call of one template at one argument
    /// digest, has that normal form and those origins, and is not normalized
    /// again.
    normalized: std.AutoHashMapUnmanaged(struct { View, u128, u128 }, Normalized) = .empty,
    /// The site's sources, in the order the walk met them (N10): a node's
    /// `SourceId` indexes this list.
    sources: std.ArrayList(Source) = .empty,
    source_ids: std.AutoHashMapUnmanaged(Source, reify.provenance.SourceId) = .empty,
    /// The provenance of every site the walk finished, in the order it did.
    published: std.ArrayList(SiteProvenance) = .empty,

    /// How many sites were normalized, which P1's counter reads.
    normalizations: u32 = 0,
    /// Where set, the site's translator returns a `Code.Bound`, so a run-time
    /// name the root reads is an input slot rather than a refusal.
    inputs: ?Inputs = null,
    /// The input slots of the site last finished, in slot order: what the
    /// program supplies for each. Owned; `takeSlots` hands it over.
    slots: []SlotSource = &.{},

    /// The run-time names a site that binds inputs reads.
    pub const Inputs = struct {
        /// The reader of the site's own module, the only module whose
        /// run-time names the call can supply.
        reader: *Reifier,
        /// Each leaf the walk numbered, by its number (`ir.Slot.Source.leaf`).
        leaves: std.ArrayList(PatternBinderId) = .empty,
    };

    /// A normal form P1 keeps: its `Graph`, its nodes' origins, and the
    /// slots its root reads, in slot order.
    const Normalized = struct {
        graph: ConstNodeId,
        /// The digests of the nodes of an `inline` view (V5a); null for `graph`.
        digests: ?ConstNodeId,
        origins: reify.provenance.Emitted,
        slot_order: []ir.SlotId,
    };

    /// What one site is built into.
    const SiteIr = struct {
        store: ir.Store,
        types: Types,
        builder: Builder,
        /// The evidence the site's calls supplied (`Reifier.supply`), which
        /// lives as long as the rows that read it.
        evidence: std.heap.ArenaAllocator,
    };

    pub fn init(gpa: Allocator, store: *ConstStore, foreign: ForeignLookup) Walk {
        return .{ .gpa = gpa, .store = store, .foreign = foreign };
    }

    pub fn deinit(self: *Walk) void {
        for (self.readers.items) |open| {
            open.deinit();
            self.gpa.destroy(open);
        }
        self.readers.deinit(self.gpa);
        self.endSite();
        self.definitions.deinit(self.gpa);
        self.rows.deinit(self.gpa);
        self.clearClosureTargets();
        self.closure_targets.deinit(self.gpa);
        var memo = self.normalized.valueIterator();
        while (memo.next()) |m| {
            m.origins.deinit(self.gpa);
            self.gpa.free(m.slot_order);
        }
        self.normalized.deinit(self.gpa);
        self.endInputs();
        self.freeSlots();
        self.sources.deinit(self.gpa);
        self.source_ids.deinit(self.gpa);
        for (self.published.items) |*p| p.deinit(self.gpa);
        self.published.deinit(self.gpa);
    }

    /// The origin of what a reader of `module` builds for the source at
    /// `region` (N10).
    pub fn originAt(self: *Walk, module: checked.CheckedModuleArtifactKey, region: base.Region) Allocator.Error!reify.provenance.OriginId {
        const source: Source = .{ .module = module, .region = region };
        const gop = try self.source_ids.getOrPut(self.gpa, source);
        if (!gop.found_existing) {
            gop.value_ptr.* = reify.provenance.SourceId.of(@intCast(self.sources.items.len));
            try self.sources.append(self.gpa, source);
        }
        return self.site.?.store.provenance.intern(self.gpa, .{ .source = gop.value_ptr.*, .via = .none });
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

    /// Start a site whose declared type selects `view`, so a site refused for
    /// one reason does not report the reason an earlier site was refused for.
    /// `binds_inputs` says whether its translator returns a `Code.Bound`, so
    /// that a run-time name the root reads is an input slot, and
    /// `site_reader` is the site module's reader.
    pub fn beginSite(self: *Walk, view: View, binds_inputs: bool, site_reader: *Reifier) void {
        self.view = view;
        self.rejection = null;
        self.endInputs();
        self.freeSlots();
        if (binds_inputs) self.inputs = .{ .reader = site_reader };
    }

    fn endInputs(self: *Walk) void {
        if (self.inputs) |*inputs| inputs.leaves.deinit(self.gpa);
        self.inputs = null;
    }

    fn freeSlots(self: *Walk) void {
        for (self.slots) |slot| {
            self.gpa.free(slot.steps);
            self.gpa.free(slot.shape);
        }
        self.gpa.free(self.slots);
        self.slots = &.{};
    }

    /// The input slots of the site last finished, which the caller now owns.
    pub fn takeSlots(self: *Walk) []SlotSource {
        const out = self.slots;
        self.slots = &.{};
        return out;
    }

    /// Forget the lambdas a first stage wrote, and free what each holds.
    fn clearClosureTargets(self: *Walk) void {
        var targets = self.closure_targets.valueIterator();
        while (targets.next()) |target| freeTarget(self.gpa, target.*);
        self.closure_targets.clearRetainingCapacity();
    }

    /// Free the instantiation and the bound callees a cloned target owns.
    fn freeTarget(gpa: Allocator, target: Reifier.CalleeTarget) void {
        if (target.instantiation) |fixed| {
            var substitution = fixed.substitution;
            substitution.deinit(gpa);
        }
        for (target.bound) |entry| freeTarget(gpa, entry.target);
        gpa.free(target.bound);
    }

    /// Give the site about to be walked a store, a type table and a builder
    /// of its own, and forget every row and type an earlier site built.
    pub fn startSite(self: *Walk) Allocator.Error!void {
        self.endSite();
        const site = try self.gpa.create(SiteIr);
        site.store = ir.Store.init(self.gpa);
        site.types = Types.init(self.gpa);
        site.builder = Builder.init(self.gpa, &site.store, &site.types);
        site.evidence = std.heap.ArenaAllocator.init(self.gpa);
        self.site = site;
        self.definitions.clearRetainingCapacity();
        self.rows.clearRetainingCapacity();
        self.clearClosureTargets();
        self.stage_one = 0;
        self.open_builtins = false;
        self.sources.clearRetainingCapacity();
        self.source_ids.clearRetainingCapacity();
        self.root = null;
        self.rejection = null;
        for (self.readers.items) |open| {
            open.ty_cache.clearRetainingCapacity();
            open.type_in_progress.clearRetainingCapacity();
            open.open_recursions.clearRetainingCapacity();
            open.nominal_in_progress.clearRetainingCapacity();
        }
    }

    fn endSite(self: *Walk) void {
        const site = self.site orelse return;
        site.builder.deinit();
        site.types.deinit();
        site.store.deinit();
        site.evidence.deinit();
        self.gpa.destroy(site);
        self.site = null;
    }

    /// Bring the site's rows, whose root is `root`, to their normal form:
    /// the simplify, finalize and number stages of `reify.driver`. A site
    /// that needs more simplify rounds than the language version allows is
    /// refused at `region`.
    pub fn normalize(self: *Walk, root: RowId, region: base.Region) error{ Rejected, OutOfMemory }!void {
        const site = self.site.?;
        const view: reify.driver.View = switch (self.view) {
            .graph => .graph,
            .inline_ => .inline_,
        };
        _ = reify.driver.runTo(self.gpa, &site.builder, root, &.{}, view) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.RoundBoundExceeded => {
                self.rejection = .{ .kind = .bound_exceeded, .region = region, .detail = "simplify rounds per component" };
                return error.Rejected;
            },
            error.UnresolvedApply => {
                self.rejection = .{ .kind = .unsupported_expression, .region = region, .detail = "a call to a function value that no simplification resolves" };
                return error.Rejected;
            },
            error.MeasureDidNotFall => invariant("a simplify round changed a row without lowering its measure"),
            error.InvariantBroken => invariant("normalization broke an invariant of the normal form"),
        };
    }

    /// The site's `Code` value: the normal form of an earlier site whose
    /// walk built the same rows (P1), or the site's rows normalized and
    /// written into the module's store. A site that needs more simplify
    /// rounds than the language version allows, or that holds a call no
    /// rule resolves, is refused at `region`.
    pub fn finish(self: *Walk, root: RowId, site_key: u64, region: base.Region) error{ Rejected, OutOfMemory }!ConstNodeId {
        const site = self.site.?;
        const walked = try reify.rows.walkedDigest(self.gpa, &site.store, &site.types, root);
        const memo_key = .{ self.view, walked ^ slotsDigest(&site.store), reify.provenance.digest(&site.store) };
        if (self.normalized.get(memo_key)) |memo| {
            try self.bindSlots(memo.slot_order, region);
            try self.publish(site_key, &memo.origins);
            var emitter = try code_emit.Emitter.init(self.gpa, self.store, &site.store, &site.types);
            defer emitter.deinit();
            if (memo.digests) |digests| return emitter.inlinedOf(memo.graph, digests, site_key);
            return emitter.siteOf(memo.graph, site_key);
        }
        try self.normalize(root, region);
        self.normalizations += 1;
        // Normalizing adds nodes, which the emitter indexes.
        var emitter = try code_emit.Emitter.init(self.gpa, self.store, &site.store, &site.types);
        defer emitter.deinit();
        self.root = root;
        const graph = try emitter.graph(root);
        const digests: ?ConstNodeId = switch (self.view) {
            .graph => null,
            .inline_ => try emitter.digests(root),
        };
        try self.bindSlots(emitter.slot_order, region);
        var origins = try reify.provenance.emitted(self.gpa, &site.store, root);
        errdefer origins.deinit(self.gpa);
        const slot_order = try self.gpa.dupe(ir.SlotId, emitter.slot_order);
        errdefer self.gpa.free(slot_order);
        try self.publish(site_key, &origins);
        try self.normalized.put(self.gpa, memo_key, .{ .graph = graph, .digests = digests, .origins = origins, .slot_order = slot_order });
        if (digests) |d| return emitter.inlinedOf(graph, d, site_key);
        return emitter.siteOf(graph, site_key);
    }

    /// A digest of the slots the walk made, which the walked rows read only
    /// by number: two sites whose rows match and whose slots differ are not
    /// one normal form.
    fn slotsDigest(store: *const ir.Store) u128 {
        var hasher = std.hash.Wyhash.init(0x5107);
        for (store.slots.items) |slot| {
            hasher.update(std.mem.asBytes(&slot.ty));
            switch (slot.source) {
                .leaf => |leaf| hasher.update(&.{ 0, @truncate(leaf), @truncate(leaf >> 8), @truncate(leaf >> 16), @truncate(leaf >> 24) }),
                .field => |f| hasher.update(std.mem.asBytes(&[_]u32{ 1, f.of.index(), f.k })),
                .index => |f| hasher.update(std.mem.asBytes(&[_]u32{ 2, f.of.index(), f.k })),
                .unwrap => |of| hasher.update(std.mem.asBytes(&[_]u32{ 3, of.index() })),
            }
        }
        const h = hasher.final();
        return @as(u128, h) << 64 | h;
    }

    /// Record, for each slot the root reads in slot order, the run-time name
    /// and the projections the program supplies it from, and refuse a slot
    /// whose type holds a shape no `Code.Value` expresses.
    fn bindSlots(self: *Walk, order: []const ir.SlotId, region: base.Region) error{ Rejected, OutOfMemory }!void {
        self.freeSlots();
        if (order.len == 0) return;
        const site = self.site.?;
        const inputs = self.inputs orelse invariant("a site whose translator binds no inputs reads an input slot");
        const out = try self.gpa.alloc(SlotSource, order.len);
        var made: usize = 0;
        errdefer {
            for (out[0..made]) |made_slot| {
                self.gpa.free(made_slot.steps);
                self.gpa.free(made_slot.shape);
            }
            self.gpa.free(out);
        }
        var steps = std.ArrayList(SlotStep).empty;
        defer steps.deinit(self.gpa);
        var shape = std.ArrayList(u32).empty;
        defer shape.deinit(self.gpa);
        for (order, out) |slot, *dest| {
            shape.clearRetainingCapacity();
            if (try slotShape(self.gpa, &site.types, inputs.reader.names, site.store.slots.items[slot.index()].ty, &shape)) |why| {
                self.rejection = .{ .kind = .input_not_bound, .region = region, .detail = why };
                return error.Rejected;
            }
            steps.clearRetainingCapacity();
            var current = slot;
            const leaf: u32 = while (true) {
                const entry = site.store.slots.items[current.index()];
                switch (entry.source) {
                    .leaf => |leaf| break leaf,
                    .field => |f| {
                        const parent_ty = site.store.slots.items[f.of.index()].ty;
                        const members = site.types.memberSlice(site.types.get(parent_ty).record);
                        const text = site.types.nameText(members[f.k].name);
                        const label = inputs.reader.names.lookupRecordFieldLabel(text) orelse
                            invariant("a field a slot reads has no label in the site's module");
                        try steps.append(self.gpa, .{ .field = label });
                        current = f.of;
                    },
                    .index => |f| {
                        try steps.append(self.gpa, .{ .index = f.k });
                        current = f.of;
                    },
                    .unwrap => |of| {
                        try steps.append(self.gpa, .unwrap);
                        current = of;
                    },
                }
            };
            std.mem.reverse(SlotStep, steps.items);
            const owned_steps = try self.gpa.dupe(SlotStep, steps.items);
            errdefer self.gpa.free(owned_steps);
            dest.* = .{
                .leaf = inputs.leaves.items[leaf],
                .steps = owned_steps,
                .shape = try self.gpa.dupe(u32, shape.items),
            };
            made += 1;
        }
        self.slots = out;
    }

    // Record the provenance of the site keyed `key`: its sources, and the
    // origins of its graph's nodes.
    fn publish(self: *Walk, key: u64, origins: *const reify.provenance.Emitted) Allocator.Error!void {
        const sources = try self.gpa.dupe(Source, self.sources.items);
        errdefer self.gpa.free(sources);
        var copy = try origins.clone(self.gpa);
        errdefer copy.deinit(self.gpa);
        try self.published.append(self.gpa, .{ .key = key, .sources = sources, .origins = copy });
    }

    /// A call reached `row`, which the walk is inside: every row from that one
    /// to the innermost reaches itself.
    pub fn markRecursive(self: *Walk, row: RowId) void {
        const from = positionOf(RowId, self.rows.items, row) orelse
            invariant("a row the walk is inside is not on its stack");
        for (self.rows.items[from..]) |inside| self.site.?.store.rows.items[inside.index()].recursive = true;
    }
};

/// The checked tables of the module being published, which the walk reads a
/// site's own bodies, plans and types from.
pub const LocalSources = struct {
    types: *const checked.CheckedTypeStore,
    bodies: *const checked.CheckedBodyStore,
    plans: *const static_dispatch.StaticDispatchPlanTable,
    names: *const canonical.CanonicalNameStore,
    artifact: checked.CheckedModuleArtifactKey,
    value_refs: *const checked.ResolvedValueRefTable,
    procedure_bindings: *const checked.TopLevelProcedureBindingTable,
    procedure_templates: *const checked.CheckedProcedureTemplateTable,
    callable_eval_templates: *const checked.CallableEvalTemplateTable,
    const_templates: *const checked.ConstTemplateTable,
    const_bodies: *const checked.CheckedConstBodyTable,
    /// What each top-level value's pattern binds, which leads a named site to
    /// the procedure binding behind the name.
    top_level_values: *const checked.TopLevelValueTable,
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
            .callable_eval_templates = self.callable_eval_templates.view(),
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
) Allocator.Error!ModuleSites {
    const sites = env.store.codeReificationSites();
    if (sites.len == 0) return .{};

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
        const bound_call: ?u32 = if (site.bound_call == @import("can").NodeStore.CodeReificationSite.no_bound_call) null else site.bound_call;
        walk.beginSite(site.view, bound_call != null, reifier);
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
            .template, .template_callee => unreachable, // template and template_callee sites were skipped by the continue above
        };
        const slots = walk.takeSlots();
        errdefer freeSlotSources(gpa, slots);
        try results.append(gpa, .{ .expr = site_expr, .outcome = outcome, .slots = slots, .bound_call = bound_call });
    }

    const outcomes = try results.toOwnedSlice(gpa);
    errdefer gpa.free(outcomes);
    return .{ .outcomes = outcomes, .provenance = try walk.published.toOwnedSlice(gpa) };
}

fn freeSlotSources(gpa: Allocator, slots: []SlotSource) void {
    for (slots) |slot| {
        gpa.free(slot.steps);
        gpa.free(slot.shape);
    }
    gpa.free(slots);
}

/// What a module's sites came to: each site's outcome, and the provenance of
/// every site that was described.
pub const ModuleSites = struct {
    outcomes: []SiteOutcome = &.{},
    provenance: []SiteProvenance = &.{},

    pub fn deinit(self: *ModuleSites, gpa: Allocator) void {
        for (self.outcomes) |outcome| freeSlotSources(gpa, outcome.slots);
        gpa.free(self.outcomes);
        for (self.provenance) |*p| p.deinit(gpa);
        gpa.free(self.provenance);
    }
};

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
    const use = local.bodies.exprIdAtRawNode(node_idx);

    // An exact function alias, `same = add_one`, has no body of its own. The
    // checker recorded the lookup it forwards to, and the site describes the
    // procedure that lookup names.
    const aliased = aliasedProcedure(walk, reifier, module, local, node_idx, region) catch |err| switch (err) {
        error.Rejected => return .{ .rejected = walk.rejection.? },
        error.OutOfMemory => |e| return e,
        error.Diverged => invariant("a divergence escaped before any row was built"),
    };
    if (aliased) |reached| {
        return reached.reader.reifyLambda(reached.body, .{
            .scheme = reached.reader.templateScheme(reached.template),
            .in_block = false,
            .caller = reifier,
            .fixed = fixed,
            .region = region,
        });
    }

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
            .use = use,
            .region = region,
        });
    }

    if (stagedDefinition(module, local, node_idx)) |staged| {
        return reifier.reifyLambda(staged.body, .{
            .scheme = reifier.templateScheme(staged.template),
            .in_block = false,
            .caller = reifier,
            .fixed = fixed,
            .use = use,
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
            .use = use,
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
        .use = use,
        .region = region,
    });
}

/// The procedure the name at `node_idx` reaches when the name is an exact
/// function alias, or null when it is not one.
///
/// A named site holds no lookup in its checked body, so the source name
/// leads to the binding: a top-level value's pattern names its procedure
/// binding, and the binding says whether it is an alias. A name of another
/// module leads to that module's export row the way a definition does.
fn aliasedProcedure(
    walk: *Walk,
    reifier: *Reifier,
    module: anytype,
    local: LocalSources,
    node_idx: u32,
    region: base.Region,
) Reifier.Error!?Reifier.ReachedProcedure {
    const data = module.expr(@as(CIR.Expr.Idx, @fromBackingInt(@intCast(node_idx)))).data;
    if (data == .e_lookup_external) {
        const external = data.e_lookup_external;
        const alias = walk.foreign.findAlias(external.module_idx, external.target_node_idx) orelse return null;
        const away = try walk.reader(alias.module);
        return try away.forwardedProcedure(alias.lookup, region);
    }
    if (data != .e_lookup_local) return null;
    const pattern_idx = data.e_lookup_local.pattern_idx;
    const pattern = local.bodies.patternIdForSource(pattern_idx) orelse return null;
    const entry = local.top_level_values.lookupByPattern(pattern) orelse return null;
    const binding = switch (entry.value) {
        .procedure_binding => |binding| binding,
        .const_ref => return null,
    };
    if (local.procedure_bindings.get(binding).body != .callable_eval_template) return null;
    return try reifier.reachedProcedure(
        .{ .top_level = .{ .artifact = local.artifact.digest(), .binding = binding } },
        local.bodies.patternBinderForSource(pattern_idx),
        region,
    );
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
