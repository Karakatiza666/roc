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
//! | a function in the site's cut (`code_primitives`) | `Prim` by its qualified name; its body is not walked (N8h) |
//! | a function outside the cut, in any package | its body, walked as one of the site's own (N8l) |
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
const checked_bodies = @import("checked_bodies.zig");
const code_analyses = @import("code_analyses.zig");
const code_output = @import("code_output.zig");
const artifact_serialize = @import("artifact_serialize.zig");
const const_store = @import("const_store.zig");
const code_emit = @import("code_emit.zig");
const code_opacity = @import("code_opacity.zig");
const static_dispatch = @import("static_dispatch_registry.zig");
const numeral = @import("types").numeral;

const Allocator = std.mem.Allocator;

const ConstNodeId = const_store.ConstNodeId;
const ConstStore = const_store.ConstStore;
const ExprId = checked_bodies.ExprId;
const PatternId = checked_bodies.PatternId;
const StatementId = checked_bodies.StatementId;
const CheckedTypeId = checked.CheckedTypeId;
const BinderId = checked_bodies.BinderId;
const CheckedBodies = checked_bodies.CheckedBodies;

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
    /// The module whose source holds `region`: the body the walk was reading
    /// (`Walk.body`), which is another module's where the walk entered a
    /// callee or a constant of that module.
    module: Module,
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
        /// A value written at a `Code` position that its translator's
        /// `Code.Bound` cannot receive as an input slot (`detail` says why).
        value_not_bound,
        /// A value site no call binds (R12) whose normal form is no data
        /// literal: the compiler cannot compute the value it is fixed to.
        value_not_computable,
        /// A site whose translator binds its inputs (`Code.Bound`), inside a
        /// generic function whose types it mentions (D1, Q4).
        bound_instance,
        /// A use whose evidence selects a method from a type alone, where no
        /// checked evidence node names the method, and the method holds an
        /// instance site: no edge keys its table (design.md "Code Instance
        /// Tables").
        instance_through_derived_evidence,
        /// A use of a template that holds an instance site, at the types of
        /// a lambda a block generalized (D1, Q5).
        instance_in_local_generic,
        /// A descriptor method (`is_eq`, `to_hash`, an eligible
        /// `to_inspect`) whose scheme needs a generic bound call's input
        /// binding, which only a written call roots (Q17, design.md "Bound
        /// Instance Roots"). `detail` names the method.
        bound_call_in_implicit_method,
        /// A platform requirement whose solution leaves a free type variable
        /// with a constraint, at an app binding that holds an instance site
        /// (design.md "Code Instance Tables"): lowering seals the variable
        /// and ignores the constraint, so no closing use describes it.
        requirement_constrained_variable,
        /// A `Code` value, or a value computed from one, inside the walked
        /// body: a lambda at a `Code` position, or a `Code.type_id` or
        /// `Code.prim` call. A description has no form for a description
        /// (D7). `detail` names the top-level constant the walk was folding,
        /// or is empty.
        code_value,
        /// A `Code.type_id` call in a generic function, at a use that fixes
        /// its proxy to a type that is no nominal (Q8).
        type_id_not_nominal,
        /// A `Code.ty_of` call whose proxy type holds a type variable that
        /// the call, or the use that reached it, leaves open (D6).
        ty_of_not_closed,
        /// A root whose checked body holds a checking error. The checker
        /// has reported that error, so publication refuses the site or the
        /// use with no report of its own.
        checking_error,
        /// A read of a function value that is a parameter of a function
        /// around the walked body. Each call can pass a different function,
        /// and its body is known only when the program runs. `detail` names
        /// the parameter.
        function_parameter,
        /// A value site at a `Code.Binds` position whose type holds an
        /// opaque type, which the checker decided after its frame finished
        /// (`CodeReificationSite.decided_late`): the `a` of its `Code(a)` was
        /// a type variable there. So no call binds it, and it has no literal.
        value_typed_late,
    };

    /// A module a refusal is placed in: its identity, and its env, which
    /// holds the source the region indexes.
    pub const Module = struct {
        artifact: checked.CheckedModuleArtifactKey,
        env: *const ModuleEnv,
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
    body: ExprId,
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
    /// The function type a call reads a generic definition at, where the
    /// checker recorded one for the call: the callable its instantiation edge
    /// related the target to (`EvidenceTargetInstantiation`), or the type a
    /// direct use instantiated the procedure's scheme at. The row's body is
    /// walked with its own function type read as this one (`instanceFrame`),
    /// so its parameters and result are this type's. Monotype specializes the
    /// target at the same callable, so a parameter the call fixed to a
    /// nominal, where the scheme has the record or tag union the checker took
    /// for it, is that nominal. Null for a use that records none, which reads
    /// its own type.
    signature: ?TyId = null,
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
    /// What the reader was opened over, which its code slots are computed
    /// from (`moduleInputs`).
    sources: Sources,
    /// This module's view of the modules in its reach.
    lookup: ForeignLookup,
    types: checked.CheckedTypeStoreView,
    bodies: CheckedBodies,
    plans: *const static_dispatch.StaticDispatchPlanTable,
    names: *const canonical.CanonicalNameStore,
    artifact: checked.CheckedModuleArtifactKey,
    value_refs: *const checked.ResolvedValueRefTable,
    procedure_bindings: *const checked.TopLevelProcedureBindingTable,
    procedure_templates: *const checked.CheckedProcedureTemplateTable,
    callable_eval_templates: checked.CallableEvalTemplateTableView,
    entry_wrappers: *const checked.EntryWrapperTable,
    const_templates: *const checked.ConstTemplateTable,
    const_bodies: *const checked.CheckedConstBodyTable,
    top_level_values: *const checked.TopLevelValueTable,
    /// The translators' cuts the module declares (I14), read from its
    /// `codeCuts` slot on first ask (`codeCuts`).
    cuts: ?*const code_analyses.CodeCutTable = null,
    /// The module's inventories (D1), read from its `codeInventories` slot
    /// on first ask (`codeInventories`). Null while `planModule` builds them
    /// for this module.
    inventories: ?*const code_analyses.CodeInventories = null,
    /// Whether `planModule` is building this module's inventories, so
    /// nothing may ask its slot for them.
    planning: bool = false,
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
    /// Keyed by id: a miss for another id of one type only builds it again.
    ty_cache: collections.DenseMapUnmanaged(CheckedTypeId, TyId) = .empty,
    /// The types `tyOf` is part way through building. Roc reaches recursion
    /// only through a nominal, and `nominalTy` closes that, so a type that
    /// reaches itself any other way has no description and is refused rather
    /// than recursed into forever.
    ///
    /// Keyed by how many nominals the walk is inside as well as the id,
    /// because a declaration's backing is one template every expansion
    /// shares: `Chain(F32)` and the `Chain(U16)` written inside it walk the
    /// same backing id under different bindings, and the second is not the
    /// first reaching itself.
    type_in_progress: std.AutoHashMapUnmanaged(TypeFrame, void) = .empty,
    /// The constants the walk is part way through folding. A definition that
    /// reads itself is refused on the repeat rather than followed forever.
    folding: collections.DenseMapUnmanaged(ExprId, void) = .empty,
    /// The iterator plan of each `for` loop by the loop's body, which keys
    /// the loop's `iter` call as a use (D1). Built on first ask.
    iter_loops: ?collections.DenseMapUnmanaged(ExprId, static_dispatch.IteratorForPlanId) = null,
    /// The block statement that binds each binder a block statement binds,
    /// keyed by the binder's raw pattern id (`definingDecl`). Built on first
    /// ask.
    defining_statements: ?collections.DenseMap(u32, StatementId) = null,
    /// The loop whose body the walk is building, or null outside one. A
    /// `break` reads it for the slots it ends the loop with.
    loop: ?Loop = null,
    /// The frame holding what the quantified variables of the definition
    /// being walked stand for. `empty_frame` while the walk is inside one that
    /// has none, which is every definition a monomorphic program writes.
    ///
    /// Set when the walk enters an instance, and restored on the way out, so
    /// one reader walks the same body once per instantiation.
    frame: FrameId = empty_frame,
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
    bound_lambda: ?ExprId = null,
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
    const FramedType = struct {
        reader: *Reifier,
        id: CheckedTypeId,
        /// The frame whose bindings the variables of `id` are read in: the
        /// instance of the definition that named the type. A binding is read
        /// where it was made, not in the frame of the definition that reads
        /// it later (Y2, D2).
        frame: FrameId,
    };

    /// An index into the walk's frames (`Walk.frames`). Each frame is the
    /// substitution of one instance a site's walk entered.
    pub const FrameId = u32;

    /// The frame of a definition with no quantified variables.
    const empty_frame: FrameId = 0;

    /// What each quantified variable of one definition stands for. Keyed by
    /// id: a variable is its own identity, never a type equal to another.
    const Substitution = collections.DenseMapUnmanaged(CheckedTypeId, FramedType);

    /// One field of a record type, beside the reader its ids are canonical in
    /// and the frame its variables are read in.
    const FieldRef = struct {
        reader: *Reifier,
        frame: FrameId,
        field: checked.CheckedRecordField,
    };

    /// One type id, at the count of nominals the walk reached it inside.
    const TypeFrame = struct {
        depth: usize,
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
        captures: []const CIR.Expr.Capture.Idx = &.{},
        /// Which definition this call fixed each function parameter of the
        /// callee to. Owned by the call, and borrowed by the walk of the
        /// callee's body.
        bound: []BoundCallee = &.{},
        /// The function type a row that replays the block around it describes
        /// at. Null for every other row, which reads its own node's type.
        at: ?CheckedTypeId = null,
        /// The callable the checker recorded for this call of a generic
        /// definition, read where the call was written. The row the call
        /// reaches is read at it (`DefinitionKey.signature`).
        signature: ?FramedType = null,
    };

    /// A template argument fixed to a value: the expression the call wrote,
    /// walked where the template's body reads the parameter.
    pub const TemplateConstant = struct {
        reader: *Reifier,
        expr: ExprId,
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
            capture: PatternId,
        };
    };

    /// What a call's callee is: a definition the walk builds a row for, a
    /// builtin, or a function in the site's cut, which is a named
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

    /// Why a callee is resolved. A description names a primitive or a
    /// function in the site's cut rather than walking it. An instance table
    /// (D1) is the table of the template the program runs, so a primitive
    /// with an inventory (an operation of a `::` type) is the definition
    /// there too.
    const CalleeUse = enum { described, instance_table };

    const Binding = struct {
        binder: BinderId,
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
            function: ExprId,
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
    const LambdaData = @FieldType(checked_bodies.ExprData, "lambda");

    /// The loop whose body the walk is building.
    const Loop = struct {
        body: RegionId,
        /// Where the slots start among the body's parameters.
        slot_base: u30,
        /// Whether the first slot is the iterator of a general loop, which a
        /// `break` hands back as it stands.
        iterator: bool,
        /// The `var`s the slots carry, in slot order after the iterator.
        carried: []const BinderId,
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
    /// The finished checked data of one module, which the walk reads that
    /// module's bodies, plans and types from.
    pub const Sources = struct {
        /// The module's bodies. Its tables hold the plans, the resolved
        /// value references, the compile-time roots, the constant and
        /// procedure templates and the top-level procedure bindings.
        bodies: CheckedBodies,
        /// The module the walk reads, so a callee that resolves to a
        /// definition of another module is recognised as one.
        artifact: checked.CheckedModuleArtifactKey,
        /// What each top-level function binding that the compiler evaluates
        /// holds. An exact alias of a function, `same = add_one`, is one of
        /// these, and its template names the lookup the alias forwards to.
        callable_eval_templates: checked.CallableEvalTemplateTableView,
        /// The entry wrapper of each compile-time root. A top-level method
        /// alias owns the scope of its binding's wrapper, whose template
        /// holds the quantified variables an edge through the alias fixes.
        entry_wrappers: *const checked.EntryWrapperTable,
        /// The bodies of the constants the compiler fixes, which the walk
        /// folds where a name reads one.
        const_bodies: *const checked.CheckedConstBodyTable,
        /// The definition each top-level value's pattern binds, which names a
        /// constant the walk reaches by its template (D1).
        top_level_values: *const checked.TopLevelValueTable,
        /// This module's methods, which name the templates the compiler
        /// calls with no written use (Q17).
        method_registry: *const static_dispatch.MethodRegistry,
    };

    fn table(comptime T: type, value: ?*const T) *const T {
        return value orelse invariant("a reified module's bodies have every publication table");
    }

    /// The sources of the module a finished artifact holds.
    pub fn artifactSources(artifact: *const checked.CheckedModuleArtifact) Sources {
        return .{
            .bodies = artifact.bodies(),
            .artifact = artifact.key,
            .callable_eval_templates = artifact.callable_eval_templates.view(),
            .entry_wrappers = &artifact.entry_wrappers,
            .const_bodies = &artifact.checked_const_bodies,
            .top_level_values = &artifact.top_level_values,
            .method_registry = &artifact.method_registry,
        };
    }

    pub fn init(walk: *Walk, module: ModuleInputs) Reifier {
        const sources = module.sources;
        const tables = sources.bodies.tables;
        return .{
            .gpa = walk.gpa,
            .walk = walk,
            .sources = sources,
            .lookup = module.lookup,
            .types = sources.bodies.types,
            .bodies = sources.bodies,
            .plans = table(static_dispatch.StaticDispatchPlanTable, tables.plans),
            .names = sources.bodies.names,
            .artifact = sources.artifact,
            .value_refs = table(checked.ResolvedValueRefTable, tables.refs),
            .procedure_bindings = table(checked.TopLevelProcedureBindingTable, tables.top_level_procedure_bindings),
            .procedure_templates = table(checked.CheckedProcedureTemplateTable, tables.templates),
            .callable_eval_templates = sources.callable_eval_templates,
            .entry_wrappers = sources.entry_wrappers,
            .const_templates = table(checked.ConstTemplateTable, tables.const_templates),
            .const_bodies = sources.const_bodies,
            .top_level_values = sources.top_level_values,
            .env = sources.bodies.env,
            .ranges = RangeNames.resolve(sources.bodies.names),
            .bool_tags = BoolTags.resolve(sources.bodies.names),
        };
    }

    /// This module's inputs, from which its code slots are computed.
    pub fn moduleInputs(self: *const Reifier) ModuleInputs {
        return .{ .sources = self.sources, .lookup = self.lookup };
    }

    /// The translators' cuts this module declares, from its `codeCuts` slot.
    pub fn codeCuts(self: *Reifier) Allocator.Error!*const code_analyses.CodeCutTable {
        if (self.cuts) |cuts| return cuts;
        const cuts = &(try self.bodies.codeCuts(self.moduleInputs())).table;
        self.cuts = cuts;
        return cuts;
    }

    /// This module's inventories, from its `codeInventories` slot.
    pub fn codeInventories(self: *Reifier) Allocator.Error!*const code_analyses.CodeInventories {
        if (self.inventories) |inventories| return inventories;
        std.debug.assert(!self.planning);
        const inventories = try self.bodies.codeInventories(self.moduleInputs());
        self.inventories = inventories;
        return inventories;
    }

    pub fn deinit(self: *Reifier) void {
        self.scope.deinit(self.gpa);
        self.ty_cache.deinit(self.gpa);
        self.type_in_progress.deinit(self.gpa);
        self.nominal_args.deinit(self.gpa);
        self.related.deinit(self.gpa);
        self.unfit.deinit(self.gpa);
        self.folding.deinit(self.gpa);
        if (self.iter_loops) |*loops| loops.deinit(self.gpa);
        if (self.defining_statements) |*defining| defining.deinit();
    }

    /// The iterator plan of the `for` loop whose body is `body`, or null.
    fn iterLoopOf(self: *Reifier, body: ExprId) Allocator.Error!?static_dispatch.IteratorForPlanId {
        if (self.iter_loops == null) {
            var loops: collections.DenseMapUnmanaged(ExprId, static_dispatch.IteratorForPlanId) = .empty;
            errdefer loops.deinit(self.gpa);
            for (0..self.bodies.nodeCount()) |index| {
                const raw: u32 = @intCast(index);
                const loop_body: ExprId = switch (self.bodies.index().nodeKind(raw)) {
                    .unreached, .pattern => continue,
                    .expr => switch (self.bodies.exprData(@fromBackingInt(raw))) {
                        .for_ => |loop| loop.body,
                        .numeral,
                        .code_site,
                        .str_segment,
                        .str,
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
                        .hosted_lambda,
                        .run_low_level,
                        => continue,
                    },
                    .statement => switch (self.bodies.statementData(@fromBackingInt(raw))) {
                        .for_ => |loop| loop.body,
                        .decl,
                        .promoted_proc,
                        .var_,
                        .var_uninitialized,
                        .reassign,
                        .crash,
                        .dbg,
                        .expr,
                        .expect,
                        .while_,
                        .infinite_loop,
                        .breakable_loop,
                        .break_,
                        .return_,
                        .rejected_method_decl,
                        .import_,
                        .alias_decl,
                        .where_alias_decl,
                        .nominal_decl,
                        .type_anno,
                        .type_var_alias,
                        .runtime_error,
                        => continue,
                    },
                };
                if (self.bodies.iteratorForPlan(raw)) |plan| try loops.put(self.gpa, loop_body, plan);
            }
            self.iter_loops = loops;
        }
        return self.iter_loops.?.get(body);
    }

    /// The static dispatch a use makes, where it is one: a `dispatch_call`,
    /// or the `iter` call of a `for` loop, keyed by the loop's body (D1).
    fn dispatchOfUse(self: *Reifier, use: ExprId) Allocator.Error!?DispatchSpec {
        switch (self.bodies.expr(use).data) {
            .dispatch_call, .method_eq, .type_dispatch_call => return DispatchSpec.ofPlan(self.plans.plans[@backingInt(self.bodies.dispatchPlan(@backingInt(use)) orelse return null)]),
            .numeral,
            .code_site,
            .str_segment,
            .str,
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
            .field_access,
            .interpolation,
            .structural_eq,
            .structural_hash,
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
        const loop = (try self.iterLoopOf(use)) orelse return null;
        const iter = self.plans.iterator_for_plans[@backingInt(loop)].iter;
        return .{ .method = iter.method, .dispatcher_ty = iter.dispatcher_ty, .resolution = iter.resolution };
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
    pub fn reifyLambda(self: *Reifier, root: ExprId, site: Site) Allocator.Error!Outcome {
        try self.walk.startSite();
        // The site's region is in the module that holds the site, until the
        // walk enters the root's body.
        self.walk.body = site.caller;
        try site.caller.relateSelectedTargets();
        try self.relateSelectedTargets();
        return self.outcomeOf(self.rootSite(root, site), site.region);
    }

    /// Describe the value site at `site_expr` (R12). A site a call binds is
    /// one input slot that holds the whole value: a root row with no
    /// parameter whose body is `Input`. Any other is the value walked as the
    /// body of a root row with no parameter, which replays the block around
    /// it as a lambda body does, and whose normal form must be a data
    /// literal (`Walk.value_literal`).
    pub fn reifyValue(self: *Reifier, site_expr: ExprId, site: Site, bound: bool) Allocator.Error!Outcome {
        try self.walk.startSite();
        self.walk.body = site.caller;
        self.walk.value_literal = !bound;
        try site.caller.relateSelectedTargets();
        try self.relateSelectedTargets();
        return self.outcomeOf(self.valueRow(site_expr, site, bound), site.region);
    }

    fn valueRow(self: *Reifier, site_expr: ExprId, site: Site, bound: bool) Error!RowId {
        const value_ty = site.fixed orelse invariant("a value site was walked with no value type");
        const opened = self.bodies.openingValueSite(site_expr);
        if (!bound and try self.bodies.exprContainsDiagnosticError(site_expr)) return self.rejectError(.checking_error, site.region, "");
        // A value written at an instance site is part of the template that
        // holds it, so it is read in that template's instance.
        var instance: ?Instantiation = if (site.enclosing) |enclosing| enclosed: {
            if (enclosing.frame == empty_frame) break :enclosed null;
            break :enclosed Instantiation{
                .substitution = try self.walk.frameSubstitution(enclosing.frame).clone(self.gpa),
                .key = enclosing.key,
            };
        } else null;
        defer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        const key = DefinitionKey{
            .artifact = self.artifact.bytes,
            .body = site_expr,
            .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            .replayed = true,
        };
        try self.walk.definitions.put(self.gpa, key, .{});
        const outer_body = self.enter();
        defer self.leave(outer_body);

        const outer_frame = self.frame;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_replay = self.replay;
        const outer_bodies = self.bodies;
        const replay: Replay = .{ .region = site.region };
        self.frame = if (instance) |fixed| try self.walk.pushFrame(fixed.substitution) else empty_frame;
        self.instance_key = key.instantiation;
        self.substitution_uses = 0;
        self.evidence = if (site.enclosing) |enclosing| enclosing.evidence else .{};
        self.replay = &replay;
        self.bodies = opened;
        defer {
            self.frame = outer_frame;
            self.instance_key = outer_instance_key;
            self.substitution_uses = outer_uses;
            self.evidence = outer_evidence;
            self.replay = outer_replay;
            self.bodies = outer_bodies;
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

        if (!bound) {
            // The literal shows the whole value, so a value whose type holds
            // an opaque type has none (10.1). Any other value is computed
            // through the bodies of the functions it calls, an opaque type's
            // operations included: what is opaque is the slot type, not the
            // functions that compute a fixed value.
            const shown = try self.placedTy(value_ty, site.region, .result);
            if (try holdsOpaque(self.gpa, self.rt(), shown)) {
                const record = self.env.codeReificationSiteForNode(ModuleEnv.nodeIdxFrom(site_expr)) orelse
                    invariant("a value site has no site record");
                // At a `Code.Binds` position such a value is an input slot
                // when the checker decided it where it is written.
                if (record.decided_late) return self.rejectError(.value_typed_late, site.region, "");
                return self.walk.refuseValueLiteral(site.region);
            }
            self.walk.readOpaqueBackings();
        }
        const result = try self.placedTy(value_ty, site.region, .result);
        const row = if (bound)
            try self.valueInputRow(site_expr, result, key, site.region)
        else
            try self.buildRow(&.{}, result, key, .{ .captures = &.{}, .lambdas = &.{}, .body = site_expr, .ret = value_ty });
        self.walk.definitions.getPtr(key).?.open = false;
        return row;
    }

    /// The root row of a value site a call binds: no parameter, and a body
    /// that delivers its one input slot, the whole value.
    fn valueInputRow(self: *Reifier, site_expr: ExprId, result: TyId, key: DefinitionKey, region: base.Region) Error!RowId {
        const inputs = if (self.walk.inputs) |*inputs| inputs else invariant("a bound value site was walked with no inputs");
        const b = self.bld();
        std.debug.assert(!b.building());
        const row = try b.beginRow(&.{}, result);
        self.walk.definitions.getPtr(key).?.row = row;
        try self.walk.rows.append(self.gpa, row);
        defer _ = self.walk.rows.pop();
        var here = [1]reify.provenance.OriginId{try self.walk.originAt(self.artifact, region)};
        const outer = b.origins;
        b.origins = &here;
        defer b.origins = outer;
        std.debug.assert(inputs.leaves.items.len == 0);
        try inputs.leaves.append(self.gpa, .{ .value = site_expr });
        const value = try b.input(result, 0);
        try b.endRow(.{ .value = &.{value} });
        return row;
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
        use: ?ExprId = null,
        region: base.Region,
        /// For an instance site (D1): the instance of the template that
        /// holds the site, which a closing use fixed. A lambda written at
        /// the site reads its `f` in that frame and with that evidence. Null
        /// for every other site.
        enclosing: ?Enclosing = null,
    };

    /// The instance of the template that holds an instance site (D1): the
    /// frame that holds what the closing use fixed its variables to, the
    /// instance's key, and the evidence the use supplied.
    pub const Enclosing = struct {
        frame: FrameId,
        key: [32]u8,
        evidence: SuppliedEvidence,
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
    fn localScheme(self: *Reifier, expr_id: ExprId) ?Scheme {
        for (self.procedure_templates.dispatch_scopes) |*scope| {
            if (scope.checked_expr != expr_id) continue;
            return .{ .vars = self.procedure_templates.scopeSchemeVars(scope), .root = scope.scheme_root };
        }
        return null;
    }

    fn rootSite(self: *Reifier, root: ExprId, site: Site) Error!RowId {
        // Publication marks each expression that holds a checking error. A
        // root so marked has its report from the checker already.
        // A lambda site is a leaf of its module's bodies, so its own body is
        // what holds the error.
        const checked_root = if (self.siteLambda(root)) |lambda| lambda.body else root;
        if (try self.bodies.exprContainsDiagnosticError(checked_root)) return self.rejectError(.checking_error, site.region, "");
        // The root is a use of its own definition, so the site fixes its
        // quantified variables the way a call fixes a callee's. The walk of
        // the root's body borrows the substitution and finishes here.
        var instance = if (site.scheme) |scheme|
            try self.instantiationOf(scheme, site.caller, site.fixed, site.use, site.region, .site)
        else if (site.enclosing) |enclosing| enclosed: {
            // A lambda written at an instance site is part of the template
            // that holds it, so it is read in that template's instance.
            if (enclosing.frame == empty_frame) break :enclosed null;
            break :enclosed Instantiation{
                .substitution = try self.walk.frameSubstitution(enclosing.frame).clone(self.gpa),
                .key = enclosing.key,
            };
        } else null;
        defer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        const key = DefinitionKey{
            .artifact = self.artifact.bytes,
            .body = root,
            .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            .replayed = site.in_block,
        };
        const at = if (site.in_block) site.fixed else null;
        // The site's lookup of the root is a use of its definition, and the
        // checker recorded on it how the use discharged the root's `where`
        // obligations, as on a call's callee. The root reads them from here,
        // as a callee reads its call's (D3).
        const supplied: SuppliedEvidence = if (site.use) |use|
            if (site.caller.plans.siteEvidence(use)) |entries| try site.caller.supply(entries, site.caller.evidence) else .{}
        else if (site.enclosing) |enclosing|
            enclosing.evidence
        else
            .{};
        return self.describeDefinition(key, instance, supplied, &.{}, at, null);
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
        // Each instance of an instance site is a description of its own
        // (D1), so its key tells it apart from the site's other instances.
        if (self.walk.instance) |instance| hasher.update(&instance);
        return hasher.final();
    }

    /// Check what each argument of a template call fixes, or say why one is
    /// not fixed. The caller releases `out` with `releaseTemplateArgs`.
    ///
    /// The arguments are written where the call is, so this runs over the
    /// calling module's stores even when the template itself is imported.
    pub fn reifyConstants(
        self: *Reifier,
        args: []const ExprId,
        out: *std.ArrayList(TemplateArg),
        gpa: Allocator,
    ) Allocator.Error!?Rejection {
        // The arguments are written at the call, in this module.
        self.walk.body = self;
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
    fn templateArg(self: *Reifier, arg_id: ExprId) Error!TemplateArg {
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
    fn templateCallee(self: *Reifier, arg_id: ExprId) Error!CalleeTarget {
        const arg = self.bodies.expr(arg_id);
        const region = arg.source_region;
        switch (arg.data) {
            .lambda, .closure => return .{
                .key = .{ .artifact = self.artifact.bytes, .body = arg_id, .replayed = true },
                .reader = self,
                .at = arg.ty,
            },
            .lookup_local => |binder| {
                if (try self.blockLambdaOf(binder)) |lambda| {
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
            .numeral,
            .code_site,
            .str_segment,
            .str,
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
    /// to a lambda. Only a block's `decl` is a defining statement.
    fn blockLambdaOf(self: *Reifier, binder: BinderId) Allocator.Error!?ExprId {
        const statement_id = try self.definingDecl(binder) orelse return null;
        const statement = self.bodies.statementData(statement_id);
        if (statement != .decl) return null;
        return if (self.lambdaOf(statement.decl.expr) != null) statement.decl.expr else null;
    }

    /// The block `decl` statement whose pattern binds `binder`, or null for a
    /// binder that a parameter, a branch, a loop, a `var` or a promoted local
    /// function binds. A lambda records what it captures by binder, and this
    /// leads from a capture back to the expression that produced its value.
    fn definingDecl(self: *Reifier, binder: BinderId) Allocator.Error!?StatementId {
        if (self.defining_statements == null) {
            self.defining_statements = try checked.boundLeafDefiningStatements(self.gpa, self.bodies);
        }
        const statement_id = self.defining_statements.?.get(@backingInt(binder)) orelse return null;
        return switch (self.bodies.statementData(statement_id)) {
            .decl => statement_id,
            .promoted_proc => null,
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
            .rejected_method_decl,
            .import_,
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            .runtime_error,
            => invariant("a defining statement is a decl or a promoted local function"),
        };
    }

    /// Describe the lambda `template` returns, with `values` written into it.
    ///
    /// `template` is the whole `Code`-returning function: its parameters are
    /// the compile-time ones, and the lambda it returns is what the stage
    /// reads. `values` is one per parameter, in order: a constant form, or
    /// the definition a function argument names.
    pub fn reifyTemplateCall(
        self: *Reifier,
        template: ExprId,
        fixing: TemplateFixing,
        values: []const TemplateArg,
        region: base.Region,
    ) Allocator.Error!Outcome {
        try self.walk.startSite();
        // `region` is the call's, in the module whose arguments the walk read
        // last (`reifyConstants`).
        std.debug.assert(self.walk.body != null);
        try fixing.caller.relateSelectedTargets();
        try self.relateSelectedTargets();
        return self.outcomeOf(self.templateSite(template, fixing, values, region), region);
    }

    /// What a template call fixes the template's quantified variables to:
    /// the template's scheme, and the type the call gives the name it calls,
    /// read in the module of the call (Q15 of
    /// roc-reify-structural-proposal.md).
    pub const TemplateFixing = struct {
        scheme: Scheme,
        /// The reader of the module the call is written in.
        caller: *Reifier,
        /// The template's function type at the call. Null where checking
        /// left the callee without a type.
        fixed: ?CheckedTypeId,
        /// The callee's lookup, which the checker keyed what the call copied
        /// the template's variables to by.
        use: ?ExprId,
    };

    /// A template call's root row. The lambda a template returns is not a
    /// definition of any module, so nothing names it and no call reaches it.
    ///
    /// The call is a use of the template, so it fixes the template's
    /// quantified variables the way a call fixes a callee's, and the body is
    /// read in a frame that holds them.
    fn templateSite(
        self: *Reifier,
        template: ExprId,
        fixing: TemplateFixing,
        values: []const TemplateArg,
        region: base.Region,
    ) Error!RowId {
        const lambda = try self.lambdaData(template);
        if (lambda.args.len != values.len) {
            return self.rejectError(.unsupported_expression, region, "a template called with the wrong number of arguments");
        }

        var instance = try self.instantiationOf(fixing.scheme, fixing.caller, fixing.fixed, fixing.use, region, .call);
        defer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        const supplied: SuppliedEvidence = if (fixing.use) |use|
            if (fixing.caller.plans.siteEvidence(use)) |entries| try fixing.caller.supply(entries, fixing.caller.evidence) else .{}
        else
            .{};
        const outer_frame = self.frame;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        self.frame = if (instance) |fixed| try self.walk.pushFrame(fixed.substitution) else empty_frame;
        self.instance_key = if (instance) |fixed| fixed.key else @splat(0);
        self.substitution_uses = 0;
        self.evidence = supplied;
        defer {
            self.frame = outer_frame;
            self.instance_key = outer_instance_key;
            self.substitution_uses = outer_uses;
            self.evidence = outer_evidence;
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
        const outer_body = self.enter();
        defer self.leave(outer_body);
        return self.lambdaRow(lambda.body, .in_scope, null, null);
    }

    /// Whether the walk describes this expression with no free names in it.
    ///
    /// A template's argument has to be one of these, because the value is
    /// walked where the template reads its parameter, in a row with none of
    /// the call's scope. A literal qualifies, and so does an aggregate every
    /// part of which does.
    fn isConstantForm(self: *Reifier, expr_id: ExprId) Allocator.Error!bool {
        return switch (self.bodies.expr(expr_id).data) {
            // A literal of the author's own type describes as the conversion
            // call beside it, which reads no name.
            .numeral, .str_segment, .bytes_literal, .empty_list, .empty_record => true,
            .str => |segments| try self.everyPartIsConstant(segments),
            .list, .tuple => |items| try self.everyPartIsConstant(items),
            .record => |record| blk: {
                if (record.ext != null) break :blk false;
                for (record.fields) |field| {
                    if (!try self.isConstantForm(self.bodies.recordFieldValue(field))) break :blk false;
                }
                break :blk true;
            },
            .nominal => |nominal| try self.isConstantForm(nominal.backing_expr),
            .tag => |tag_expr| try self.everyPartIsConstant(tag_expr.args),
            .zero_argument_tag => true,
            // A name is the form the value it holds is, which is what lets a
            // template argument be written as one.
            .lookup_local, .lookup_external, .lookup_required => try self.nameHoldsConstant(self.bodies.resolvedRef(expr_id)),
            .anno_only,
            .binop,
            .block,
            .break_,
            .call,
            .closure,
            .code_site,
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
            .return_,
            .run_low_level,
            .runtime_error,
            .structural_eq,
            .structural_hash,
            .tuple_access,
            .type_dispatch_call,
            .unary_minus,
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

    fn everyPartIsConstant(self: *Reifier, parts: []const ExprId) Allocator.Error!bool {
        for (parts) |part| {
            if (!try self.isConstantForm(part)) return false;
        }
        return true;
    }

    // Rows //

    /// The parameters and body of the lambda an expression is, looking through
    /// a closure whose captures the row takes or the scope holds.
    fn lambdaData(self: *Reifier, expr_id: ExprId) Error!LambdaData {
        const expr = self.bodies.expr(expr_id);
        return self.lambdaOf(expr_id) orelse self.rejectError(.unsupported_expression, expr.source_region, exprFormName(expr.data));
    }

    /// The lambda of a `Code` site written as a lambda or a closure, or null
    /// for any other node. `exprData` reads such a site as a leaf; the walk
    /// of the site reads its lambda.
    fn siteLambda(self: *Reifier, expr_id: ExprId) ?checked_bodies.CodeSiteLambda {
        if (!self.bodies.index().isCodeSite(expr_id)) return null;
        const tag = self.bodies.nodeTag(@backingInt(expr_id));
        if (tag != .expr_lambda and tag != .expr_closure) return null;
        return self.bodies.codeSiteLambda(expr_id);
    }

    /// The lambda an expression is, looking through a closure, or null when it
    /// is not one.
    fn lambdaOf(self: *Reifier, expr_id: ExprId) ?LambdaData {
        if (self.siteLambda(expr_id)) |site| return .{ .args = site.args, .body = site.body };
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
    fn isCurried(self: *Reifier, body: ExprId) bool {
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
    fn boundCapture(self: *Reifier, lambda: ExprId, pattern: PatternId) ?u32 {
        if (self.bound_lambda != lambda) return null;
        return capturedCallee(self.bound, pattern);
    }

    /// The entry of `bound` that fixes a captured name, as an index into it.
    fn capturedCallee(bound: []const BoundCallee, pattern: PatternId) ?u32 {
        for (bound, 0..) |entry, slot| {
            switch (entry.param) {
                .capture => |captured| if (captured == pattern) return @intCast(slot),
                .position => {},
            }
        }
        return null;
    }

    /// The bound callee a name in scope stands for, when a call fixed it.
    fn calleeInScope(self: *Reifier, pattern: PatternId) ?u32 {
        const binding = self.lookupBinding(pattern) orelse return null;
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
    fn stagedFunctionTypeId(self: *Reifier, expr: checked_bodies.Expr) CheckedTypeId {
        if (self.functionOf(expr.ty) != null) return expr.ty;
        if (self.siteLambda(expr.id)) |site| return self.bodies.expr(site.lambda).ty;
        if (expr.data != .closure) return expr.ty;
        return self.bodies.expr(expr.data.closure.lambda).ty;
    }

    /// What a lambda captured from around itself, empty when it captured
    /// nothing. A plain lambda is the closure's body and holds none.
    fn capturesOf(self: *Reifier, expr_id: ExprId) []const CIR.Expr.Capture.Idx {
        if (self.siteLambda(expr_id)) |site| return site.captures;
        const data = self.bodies.exprData(expr_id);
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
        /// The callable the call recorded (`CalleeTarget.signature`).
        signature: ?FramedType,
    ) Error!RowId {
        std.debug.assert(std.meta.eql(key.artifact, self.artifact.bytes));
        try self.relateSelectedTargets();
        try self.walk.definitions.put(self.gpa, key, .{});
        // The signature and the body are this module's source.
        const outer_body = self.enter();
        defer self.leave(outer_body);

        const outer_frame = self.frame;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        const outer_replay = self.replay;
        const replay: Replay = .{ .region = self.bodies.expr(key.body).source_region };
        self.frame = try self.instanceFrame(instance, signature, key.body, key.curried);
        self.instance_key = key.instantiation;
        self.substitution_uses = 0;
        self.evidence = supplied;
        self.bound = bound;
        self.bound_lambda = key.body;
        self.replay = if (at != null) &replay else null;
        defer {
            self.frame = outer_frame;
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
        expr_id: ExprId,
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
            return self.rejectCodeValue(region);
        // A stage runs this description during `roc build`, where an effect has
        // nowhere to happen. `tyOf` refuses an effectful function everywhere
        // else; the staged lambda's own type is the one that never reaches it.
        if (staged_fn.kind == .effectful) return self.rejectError(.effect, region, "this function's own type is effectful (`=>`)");
        if (staged_fn.args.len != lambda.args.len) return self.rejectError(.unsupported_expression, region, "lambda");

        var params = std.ArrayList(TyId).empty;
        defer params.deinit(self.gpa);
        switch (captures) {
            .parameter => for (captured) |capture_id| {
                const capture = self.bodies.capture(capture_id);
                if (self.boundCapture(expr_id, capture.pattern) != null) continue;
                const pattern = self.bodies.pattern(capture.pattern);
                try params.append(self.gpa, try self.tyOf(pattern.ty, pattern.source_region));
            },
            // A capture of a name the scope already holds needs nothing at run
            // time: a template call fixed it, or the root replays the
            // statement that binds it. A name from outside the staged
            // function stays the refusal it has always been.
            .in_scope => for (captured) |capture_id| {
                const capture = self.bodies.capture(capture_id);
                if (self.capturedInScope(capture.pattern)) continue;
                if (try self.replayStatement(capture.pattern) != null) continue;
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
        const lambdas = [_]ExprId{expr_id};
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
    fn curriedLambdaRow(self: *Reifier, expr_id: ExprId, key: DefinitionKey) Error!RowId {
        const region = self.bodies.expr(expr_id).source_region;
        const outer = try self.lambdaData(expr_id);
        var params = std.ArrayList(TyId).empty;
        defer params.deinit(self.gpa);
        const lambdas = [_]ExprId{ expr_id, outer.body };
        var ret: CheckedTypeId = undefined;
        for (lambdas) |lambda_id| {
            const lambda = try self.lambdaData(lambda_id);
            const fn_ty = self.functionOf(self.stagedFunctionTypeId(self.bodies.expr(lambda_id))) orelse
                return self.rejectCodeValue(region);
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
        captures: []const CIR.Expr.Capture.Idx,
        lambdas: []const ExprId,
        body: ExprId,
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
        for (parts.captures) |capture_id| {
            const capture = self.bodies.capture(capture_id);
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
        // Same type, not same id: two ids can name one closed type.
        if (!parts.demanded and try self.types.sameType(parts.ret, self.bodies.valueType(parts.body))) return self.exprRef(parts.body);
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
        // The signature is read in the site's own types, where the row is.
        if (target.signature) |callable| {
            target.key.signature = try callable.reader.tyOfIn(callable.frame, callable.id, target.reader.bodies.expr(target.key.body).source_region);
        }
        if (self.walk.definitions.get(target.key)) |existing| {
            const row = existing.row orelse invariant("a call reached a definition before its row began");
            if (existing.open) self.walk.markRecursive(row);
            return row;
        }
        return target.reader.describeDefinition(target.key, target.instantiation, target.evidence, target.bound, target.at, target.signature);
    }

    /// A lambda written where a value stands: a closure of its row, over what
    /// it captured (N8b).
    ///
    /// `at` is the function type the lambda is read at. The checker takes a
    /// record or a tag union for the nominal that declares it, so a lambda
    /// that builds one and is read at a function of the nominal delivers the
    /// nominal: its row is built at it.
    fn closureAt(self: *Reifier, expr_id: ExprId, at: ?TyId) Error!Ref {
        const expr = self.bodies.expr(expr_id);
        // A lambda the checker generalized where it stands (a parameter only a
        // method call reads, `|values| values.with_index()`) is read at the
        // instance the checker recorded for that place, as Monotype lowers it
        // at the function type its place requests.
        var instance = if (self.localScheme(expr_id)) |scheme|
            try self.instantiationOf(scheme, self, null, expr_id, expr.source_region, .call)
        else
            null;
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        const fn_ty = if (instance) |fixed|
            try self.tyOfIn(try self.walk.pushFrame(fixed.substitution), self.stagedFunctionTypeId(expr), expr.source_region)
        else
            try self.tyOf(self.stagedFunctionTypeId(expr), expr.source_region);
        const local = instance;
        instance = null;
        var target = try self.enclosedLambda(expr_id, local, self.capturesOf(expr_id));
        if (local != null) {
            if (self.plans.siteEvidence(expr_id)) |supplied| target.evidence = try self.supply(supplied, self.evidence);
        }
        target.key.result = self.readAsNominal(fn_ty, at);
        const closure_ty = if (target.key.result != null) at.? else fn_ty;
        if (self.walk.stage_one == 0) return self.closureOf(target, closure_ty);
        // A lambda a first stage writes may be applied before the stage ends,
        // where the walk stands, so its target is kept beside its row.
        const kept = try self.boundTarget(target);
        errdefer Walk.freeTarget(self.gpa, kept);
        const closure = try self.closureOf(target, closure_ty);
        const known = self.bld().knownClosure(closure) orelse invariant("a lambda's closure is a Closure node");
        const previous = self.walk.closure_targets.get(known.row);
        try self.walk.closure_targets.put(self.gpa, known.row, kept);
        if (previous) |old| Walk.freeTarget(self.gpa, old);
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
        expr_id: ExprId,
        local: ?Instantiation,
        captures: []const CIR.Expr.Capture.Idx,
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
        for (captures) |capture_id| {
            const captured = self.bodies.capture(capture_id).pattern;
            const index = self.calleeInScope(captured) orelse continue;
            try bound.append(self.gpa, .{ .param = .{ .capture = captured }, .target = try self.boundTarget(self.bound[index].target) });
        }
        if (self.walk.frameSubstitution(self.frame).count() != 0) {
            var merged = try self.walk.frameSubstitution(self.frame).clone(self.gpa);
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
        for (target.captures) |capture_id| {
            const captured = self.bodies.capture(capture_id).pattern;
            if (capturedCallee(target.bound, captured) != null) continue;
            const pattern = self.bodies.pattern(captured);
            try values.append(self.gpa, try self.lookupRef(captured, null, pattern.ty, null, null, pattern.source_region));
        }
        const row = try self.calledRow(target);
        return self.bld().closure(row, values.items, fn_ty);
    }

    /// The frame a definition's body is walked in: what the call fixed its
    /// quantified variables to, and, where the call recorded the callable it
    /// reads the definition at (`CalleeTarget.signature`), each parameter and
    /// result of the definition's own function type read as that callable's.
    ///
    /// This is the relation Monotype makes between a target's function type
    /// and the callable it is specialized at (`relateFunctionRequestInterface`).
    /// The checker took a record or a tag union for a parameter the call fixed
    /// to a nominal, and the definition's own type keeps the record, so the
    /// callable is what says the nominal. Every node of the body whose type is
    /// that parameter's then reads the nominal: a call that passes it on reads
    /// its callee at the nominal too. A variable the call fixed keeps what the
    /// call fixed it to. `curried` relates the inner lambda of a curried
    /// definition to the function the callable returns.
    fn instanceFrame(self: *Reifier, instance: ?Instantiation, signature: ?FramedType, body: ExprId, curried: bool) Error!FrameId {
        const callable = signature orelse return if (instance) |fixed| self.walk.pushFrame(fixed.substitution) else empty_frame;
        var related: Substitution = if (instance) |fixed| try fixed.substitution.clone(self.gpa) else .empty;
        defer related.deinit(self.gpa);
        var lambda_id = body;
        var at = callable;
        var remaining: usize = if (curried) 2 else 1;
        while (true) {
            const own = self.functionOf(self.stagedFunctionTypeId(self.bodies.expr(lambda_id))) orelse
                invariant("a definition a call reads at its callable is a lambda of a function type");
            const called = at.reader.functionOf(at.id) orelse invariant("a call's recorded callable is a function");
            if (own.args.len != called.args.len) invariant("a call's callable takes the parameters its callee's lambda does");
            for (own.args, called.args) |arg, called_arg| try self.relateType(&related, arg, at.reader.resolvedTypeIn(at.frame, called_arg));
            const result = at.reader.resolvedTypeIn(at.frame, called.ret);
            try self.relateType(&related, own.ret, result);
            remaining -= 1;
            if (remaining == 0) break;
            lambda_id = (try self.lambdaData(lambda_id)).body;
            at = result;
        }
        return self.walk.pushFrame(related);
    }

    /// Read one type of a definition's own function type as the callable's
    /// type at that position, and every type inside it as the callable's type
    /// at the same position inside, as Monotype's graph unification relates
    /// the nodes below the two roots it joins (`unifyRoots`). A type the
    /// relation already reads, a variable the call fixed among them, keeps
    /// what it reads, which also ends the walk of a recursive type.
    ///
    /// The definition's side is a type of this store, and the callable's side
    /// is a type of the store and frame the call recorded it in. Positions
    /// pair as unification pairs them: a function's parameters and result, a
    /// tuple's elements, a record's fields by name, a tag union's variants by
    /// name and their payloads, and a nominal's arguments where both sides
    /// are that nominal. A record or a tag union of the definition's side that
    /// the callable's side holds a nominal for is the lift the checker made
    /// (unify.zig `unifyRecordWithNominal`), and pairs with the nominal's
    /// backing at the callable's arguments, as Monotype's
    /// `unifyThroughBacking` does. A row variable is not paired: the record or
    /// tag union that stands on it is, as a whole.
    fn relateType(self: *Reifier, related: *Substitution, own: CheckedTypeId, called: FramedType) Error!void {
        // Keyed by id: the relation pairs the positions of the definition's
        // own type, and a body node at a position has that position's id.
        const entry = try related.getOrPut(self.gpa, own);
        if (entry.found_existing) return;
        entry.value_ptr.* = called;
        try self.relateInside(related, own, called);
    }

    /// The pairing of `relateType` below one pair of positions.
    fn relateInside(self: *Reifier, related: *Substitution, own: CheckedTypeId, raw_called: FramedType) Error!void {
        const called = settledType(raw_called);
        const called_payload = called.reader.types.payload(called.id);
        // A position the callable leaves open fixes nothing inside.
        switch (called_payload) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .flex, .rigid, .pending, .err => return,
            .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => {},
            .alias => unreachable, // settledType reads through every alias
        }
        switch (self.types.payload(own)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| try self.relateType(related, alias.backing, called),
            .flex, .rigid, .pending, .err, .empty_record, .empty_tag_union => {},
            .function => |own_fn| {
                const called_fn = switch (called_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .function => |function| function,
                    .record, .tuple, .nominal, .empty_record, .tag_union, .empty_tag_union, .flex, .rigid, .pending, .err, .alias => invariant("a function type of a definition relates to a function of its callable"),
                };
                if (own_fn.args.len != called_fn.args.len) invariant("a function type of a definition takes the parameters the callable's does");
                for (own_fn.args, called_fn.args) |arg, called_arg| try self.relateType(related, arg, called.reader.resolvedTypeIn(called.frame, called_arg));
                try self.relateType(related, own_fn.ret, called.reader.resolvedTypeIn(called.frame, called_fn.ret));
            },
            .tuple => |own_elements| {
                const called_elements = switch (called_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .tuple => |elements| elements,
                    .record, .function, .nominal, .empty_record, .tag_union, .empty_tag_union, .flex, .rigid, .pending, .err, .alias => invariant("a tuple of a definition relates to a tuple of its callable"),
                };
                if (own_elements.len != called_elements.len) invariant("a tuple of a definition has the elements the callable's does");
                for (own_elements, called_elements) |element, called_element| try self.relateType(related, element, called.reader.resolvedTypeIn(called.frame, called_element));
            },
            .nominal => |own_nominal| {
                const called_nominal = switch (called_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .nominal => |nominal| nominal,
                    .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union, .flex, .rigid, .pending, .err, .alias => invariant("a nominal of a definition relates to that nominal of its callable"),
                };
                if (!self.sameTypeName(own_nominal.name, called.reader, called_nominal.name) or own_nominal.args.len != called_nominal.args.len) {
                    invariant("a nominal of a definition relates to that nominal of its callable");
                }
                for (own_nominal.args, called_nominal.args) |arg, called_arg| try self.relateType(related, arg, called.reader.resolvedTypeIn(called.frame, called_arg));
            },
            .record => |own_record| switch (called_payload) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .record => |called_record| {
                    var own_fields = std.ArrayList(checked.CheckedRecordField).empty;
                    defer own_fields.deinit(self.gpa);
                    try self.recordFields(&own_fields, own_record.fields, own_record.ext);
                    var called_fields = std.ArrayList(checked.CheckedRecordField).empty;
                    defer called_fields.deinit(self.gpa);
                    try called.reader.recordFields(&called_fields, called_record.fields, called_record.ext);
                    for (own_fields.items) |field| {
                        // A field the definition's kind lets a record omit
                        // (`?` or a default) pairs with nothing where the
                        // callable's record omits it.
                        const match = for (called_fields.items) |called_field| {
                            if (self.sameFieldLabel(field.name, called.reader, called_field.name)) break called_field;
                        } else switch (field.kind.tag) {
                            .required => invariant("a required field of a definition's record is a field of its callable's"),
                            .optional, .defaulted, .undetermined, .err => continue,
                        };
                        try self.relateType(related, field.ty, called.reader.resolvedTypeIn(called.frame, match.ty));
                    }
                },
                .nominal => |called_nominal| try self.relateInside(related, own, try called.reader.nominalBacking(called, called_nominal)),
                .tuple, .function, .empty_record, .tag_union, .empty_tag_union, .flex, .rigid, .pending, .err, .alias => invariant("a record of a definition relates to a record of its callable, or to a nominal it lifted into"),
            },
            .tag_union => |own_union| switch (called_payload) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .tag_union => |called_union| {
                    var own_tags = std.ArrayList(checked.CheckedTag).empty;
                    defer own_tags.deinit(self.gpa);
                    try self.unionTags(&own_tags, own_union.tags, own_union.ext);
                    var called_tags = std.ArrayList(checked.CheckedTag).empty;
                    defer called_tags.deinit(self.gpa);
                    try called.reader.unionTags(&called_tags, called_union.tags, called_union.ext);
                    for (own_tags.items) |variant| {
                        const match = for (called_tags.items) |called_variant| {
                            if (self.sameTagLabel(variant.name, called.reader, called_variant.name)) break called_variant;
                        } else invariant("a variant of a definition's tag union is a variant of its callable's");
                        const payloads = variant.args;
                        const called_payloads = match.args;
                        if (payloads.len != called_payloads.len) invariant("a variant of a definition carries the payloads its callable's does");
                        for (payloads, called_payloads) |payload, called_arg| try self.relateType(related, payload, called.reader.resolvedTypeIn(called.frame, called_arg));
                    }
                },
                .nominal => |called_nominal| try self.relateInside(related, own, try called.reader.nominalBacking(called, called_nominal)),
                .record, .tuple, .function, .empty_record, .empty_tag_union, .flex, .rigid, .pending, .err, .alias => invariant("a tag union of a definition relates to a tag union of its callable, or to a nominal it lifted into"),
            },
        }
    }

    /// `type`, read through what its frame fixes it to and through every
    /// alias, to the structure or variable it stands for.
    fn settledType(framed: FramedType) FramedType {
        var current = framed;
        while (true) {
            if (current.reader.fixedTypeIn(current.frame, current.id)) |fixed| {
                current = fixed;
                continue;
            }
            switch (current.reader.types.payload(current.id)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .alias => |alias| current.id = alias.backing,
                .flex, .rigid, .pending, .err, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => return current,
            }
        }
    }

    /// The backing of a nominal of this store, read in a frame that fixes the
    /// declaration's variables to the arguments `framed` gives them.
    fn nominalBacking(self: *Reifier, framed: FramedType, nominal: checked.CheckedNominalType) Error!FramedType {
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            invariant("a nominal a definition's structure lifted into has a backing");
        if (nominal.args.len == 0) return .{ .reader = self, .id = backing, .frame = empty_frame };
        const declaration = self.types.nominalDeclarationForPayload(nominal) orelse
            invariant("a nominal a definition's structure lifted into has a declaration");
        const formals = declaration.formalArgs(self.types);
        if (formals.len != nominal.args.len) invariant("a nominal's arguments are its declaration's variables");
        var fixed: Substitution = .empty;
        defer fixed.deinit(self.gpa);
        for (formals, nominal.args) |formal, arg| try fixed.put(self.gpa, formal, self.resolvedTypeIn(framed.frame, arg));
        return .{ .reader = self, .id = backing, .frame = try self.walk.pushFrame(fixed) };
    }

    /// The type the term `term` of `terms`, a term of this store, stands for
    /// with its free variables read in `frame` (Q17). A term with bindings
    /// is read in a frame that fixes each bound variable to its term.
    fn termType(self: *Reifier, terms: TypeTerms, term: u32, frame: FrameId) Allocator.Error!FramedType {
        const found = terms.terms[term];
        const bindings = terms.termBindings(found);
        if (bindings.len == 0) return self.resolvedTypeIn(frame, found.ty);
        var fixed: Substitution = .empty;
        defer fixed.deinit(self.gpa);
        for (bindings) |binding| try fixed.put(self.gpa, binding.variable, try self.termType(terms, binding.term, frame));
        return .{ .reader = self, .id = found.ty, .frame = try self.walk.pushFrame(fixed) };
    }

    /// The instance of the template a descriptor method of `owner`'s nominal
    /// runs at `owner` (Q17): the reader of its module, the body it runs,
    /// the frame that holds what the owner fixed its variables to, and the
    /// instance's key.
    const ImplicitInstance = struct {
        reader: *Reifier,
        body: ExprId,
        frame: FrameId,
        key: [32]u8,
    };

    fn implicitInstance(owner: FramedType, method: DescriptorMethod, region: base.Region) Error!ImplicitInstance {
        const settled = settledType(owner);
        const nominal = settled.reader.nominalOf(settled.id) orelse
            invariant("a descriptor method's owner type is a nominal");
        const declaring = try settled.reader.templateReader(.{ .bytes = nominal.owner_module.bytes }) orelse
            invariant("a descriptor method's owner is declared in a module the walk cannot read");
        const target = declaringMethod(declaring, settled.reader.foreignNominal(nominal), method) orelse
            invariant("a descriptor method an occurrence names has no target");
        const found = try implicitTargetOf(declaring, target) orelse
            invariant("a descriptor method an occurrence names runs no template");
        const reader = try settled.reader.templateReader(.{ .bytes = found.artifact }) orelse
            invariant("a descriptor method's template is in a module the walk cannot read");
        const template = reader.procedure_templates.templates.items[@backingInt(found.template)];
        // A computed callable's entry wrapper returns the method's function.
        const method_fn = if (found.computed)
            (reader.functionOf(template.checked_fn_root) orelse invariant("an entry wrapper's type is a function")).ret
        else
            template.checked_fn_root;
        const params = (reader.functionOf(method_fn) orelse invariant("a descriptor method's type is a function")).args;
        if (params.len == 0) invariant("a descriptor method takes its owner first");
        var instance = try reader.instantiationAtOwner(.{ .vars = reader.schemeVars(template), .root = method_fn }, params[0], settled, region);
        defer if (instance) |*fixed| fixed.substitution.deinit(reader.gpa);
        return .{
            .reader = reader,
            .body = found.body,
            .frame = if (instance) |fixed| try reader.walk.pushFrame(fixed.substitution) else empty_frame,
            .key = if (instance) |fixed| fixed.key else @splat(0),
        };
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
            return self.rejectCodeValue(region);
        try self.relateSelectedTargets();
        try self.folding.put(self.gpa, lambda_id, {});
        defer _ = self.folding.remove(lambda_id);

        const outer_frame = self.frame;
        const outer_instance_key = self.instance_key;
        const outer_uses = self.substitution_uses;
        const outer_evidence = self.evidence;
        const outer_bound = self.bound;
        const outer_bound_lambda = self.bound_lambda;
        const outer_replay = self.replay;
        self.frame = try self.instanceFrame(target.instantiation, target.signature, lambda_id, false);
        self.instance_key = target.key.instantiation;
        self.substitution_uses = 0;
        self.evidence = target.evidence;
        self.bound = target.bound;
        self.bound_lambda = lambda_id;
        self.replay = null;
        defer {
            self.frame = outer_frame;
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

        // The call's region is the caller's, so the result type is read
        // before the walk enters this module's source.
        const result = at orelse target.key.result orelse try self.tyOf(fn_ty.ret, region);
        const outer_body = self.enter();
        defer self.leave(outer_body);

        var next: usize = 0;
        for (target.captures) |capture_id| {
            const capture = self.bodies.capture(capture_id);
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

        // Same type, not same id: two ids can name one closed type.
        const walked = if (at == null and target.key.result == null and try self.types.sameType(fn_ty.ret, self.bodies.valueType(lambda.body)))
            self.exprRef(lambda.body)
        else
            self.exprAt(lambda.body, result);
        return walked catch |err| switch (err) {
            error.Diverged => invariant("a body the scan found no exit in diverged"),
            error.Rejected, error.OutOfMemory => |e| return e,
        };
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

    fn lookupBinding(self: *Reifier, binder: BinderId) ?Binding {
        var index = self.scope.items.len;
        while (index > 0) {
            index -= 1;
            if (self.scope.items[index].binder == binder) return self.scope.items[index];
        }
        return null;
    }

    /// Put the binder an `assign` pattern binds in scope. Any other pattern is
    /// refused: only a name can stand for what `kind` holds.
    fn bindName(self: *Reifier, pattern_id: PatternId, kind: Binding.Kind, region: base.Region) Error!void {
        const binder = switch (self.bodies.patternData(pattern_id)) {
            .assign => pattern_id,
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

    fn bindValue(self: *Reifier, binder: BinderId, value: Ref) Allocator.Error!void {
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
    fn boundBefore(self: *Reifier, binder: BinderId, len: usize) bool {
        for (self.scope.items[0..len]) |binding| {
            if (binding.binder == binder) return true;
        }
        return false;
    }

    /// The binder a pattern is, or null for a pattern that is none: an
    /// assign, var or as pattern, and a literal pattern whose comparison
    /// dispatches, which binds the matched value, are binders.
    fn binderOf(self: *Reifier, pattern_id: PatternId) ?BinderId {
        return switch (self.bodies.patternData(pattern_id)) {
            .assign, .as => pattern_id,
            .numeral_literal, .str_literal => if (self.bodies.literalPatternIsCustom(pattern_id)) pattern_id else null,
            .applied_tag,
            .nominal,
            .record_destructure,
            .list,
            .tuple,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => null,
        };
    }

    /// Whether a capture names something the scope already binds.
    fn capturedInScope(self: *Reifier, pattern_id: PatternId) bool {
        return self.lookupBinding(pattern_id) != null;
    }

    /// What a capture is called, for the refusal that names it.
    fn capturedName(self: *Reifier, pattern_id: PatternId) []const u8 {
        return self.binderName(pattern_id);
    }

    /// The statement that binds a name the root reads from the block around
    /// it, or null where nothing replays it: no root is being walked, or the
    /// statement sits inside the root and the walk binds it there.
    fn replayStatement(self: *Reifier, pattern_id: PatternId) Allocator.Error!?StatementId {
        return self.replayStatementOf(pattern_id);
    }

    fn replayStatementOf(self: *Reifier, binder: BinderId) Allocator.Error!?StatementId {
        const replay = self.replay orelse return null;
        const statement_id = try self.definingDecl(binder) orelse return null;
        const statement = self.bodies.statement(statement_id).source_region;
        if (statement.start.offset >= replay.region.start.offset and statement.end.offset <= replay.region.end.offset) return null;
        return statement_id;
    }

    /// Resolve a name the root reads from the block around it: the statement
    /// that binds it is walked here, where the root first reads it, and binds
    /// its names in the scope that reads them. A statement reads only what
    /// the statements before it bind, so a replay that reads another name
    /// replays that statement first.
    fn replayBinding(self: *Reifier, binder: BinderId) Error!?Binding {
        const statement_id = try self.replayStatementOf(binder) orelse return null;
        const decl = switch (self.bodies.statementData(statement_id)) {
            .decl => |decl| decl,
            // A promoted local function has no value to replay: every use of
            // its name resolves to its procedure.
            .promoted_proc,
            .rejected_method_decl,
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

    /// The name the source wrote for `binder`, read from the ident store of
    /// the module that owns it: an associated item's declared method name,
    /// and otherwise the identifier the canonicalizer recorded on the
    /// binding pattern.
    fn binderName(self: *Reifier, binder: BinderId) []const u8 {
        // An associated item's pattern binds its qualified name (`Lib.scale`);
        // the name its declaration wrote is the method identifier its owner
        // registered it under.
        for (self.env.method_defs.entries.items) |entry| {
            if (self.env.store.getDef(entry.value.def_idx).pattern == binder) return self.env.getIdentText(entry.key.methodIdent());
        }
        const name = switch (self.env.store.getPattern(binder)) {
            .assign => |assign| assign.ident,
            .var_assign => |assign| assign.ident,
            .as => |as_pattern| as_pattern.ident,
            // Only a literal pattern's matched value is a binder with no
            // name, and no capture, parameter or exported function is one.
            .applied_tag,
            .nominal,
            .nominal_external,
            .deferred_import_ref,
            .record_destructure,
            .list,
            .tuple,
            .num_literal,
            .small_dec_literal,
            .dec_literal,
            .frac_f32_literal,
            .frac_f64_literal,
            .num_from_numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => invariant("a named binder is an assign, var or as pattern"),
        };
        return self.env.getIdentText(name);
    }

    // Values //

    /// Bind the names an irrefutable pattern binds, each to the part of
    /// `value` it names: a record's `Field`, a tuple's `Index`, a single
    /// variant's `Payload` (N1f). A pattern that can fail belongs to a
    /// `match`, and is refused here.
    fn bindPattern(self: *Reifier, pattern_id: PatternId, value: Ref) Error!void {
        const pattern = self.bodies.pattern(pattern_id);
        const region = pattern.source_region;
        const b = self.bld();
        switch (pattern.data) {
            .assign => try self.bindValue(pattern_id, value),
            .underscore => {},
            .as => |renamed| {
                try self.bindValue(pattern_id, value);
                try self.bindPattern(renamed.pattern, value);
            },
            .record_destructure => |destructs| {
                const record = try self.readable(value);
                for (destructs) |destruct_id| {
                    const destruct = self.bodies.recordDestruct(destruct_id);
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
                const tag_name = try self.tagName(union_ty, self.names.tagLabelText(self.bodies.tagLabel(applied.name)), region);
                for (applied.args, 0..) |arg, k| try self.bindPattern(arg, try b.payload(subject, tag_name, @intCast(k)));
            },
            .list,
            .numeral_literal,
            .str_literal,
            .str_interpolation,
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

    fn exprRef(self: *Reifier, expr_id: ExprId) Error!Ref {
        return self.exprAs(expr_id, null);
    }

    /// The value of `expr_id` built at `at`, the type its position fixes.
    ///
    /// The two differ where a value is used at a wider tag union than its
    /// own: a lambda body composes a `?` result, whose error row holds every
    /// tag of the body's own (design.md "Try Return-Row Composition"), or the
    /// checker recorded a row coercion (design.md "Row Coercion Primitive").
    /// A node's own row coercion is read at `at` too.
    /// A constructor builds at `at` directly, and a branching construct or
    /// block builds each of its values there. Any other value is built at
    /// its own type and lifted to `at` (`liftTo`): conformance where the
    /// step widens a union, `Wrap` where it lifts a union into a nominal. A
    /// call is built at the union `liftReach` gives, and lifted from there.
    fn exprAt(self: *Reifier, expr_id: ExprId, at: TyId) Error!Ref {
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        const outer_body = self.enter();
        defer self.leave(outer_body);
        var here = [1]reify.provenance.OriginId{try self.walk.originAt(self.artifact, region)};
        const outer = self.bld().origins;
        self.bld().origins = &here;
        defer self.bld().origins = outer;
        return switch (expr_data.data) {
            .tag, .zero_argument_tag, .nominal => self.ownAs(expr_id, at),
            // A call whose result is read at a wider union has that union as its type.
            .call => |call| blk: {
                const reached = try self.liftReach(try self.tyOf(expr_data.ty, region), at);
                break :blk self.liftTo(try self.callExpr(call.func, call.args, expr_data.ty, reached, region), at, region);
            },
            // A constant a name folds to is built at `at`.
            .lookup_local => |pattern| self.liftTo(try self.lookupRef(pattern, self.bodies.resolvedRef(expr_id), expr_data.ty, expr_id, at, region), at, region),
            .lookup_external, .lookup_required => blk: {
                if (try self.foldedConstant(self.bodies.resolvedRef(expr_id), expr_data.ty, at, region)) |folded| break :blk self.liftTo(folded, at, region);
                break :blk self.liftTo(try self.ownAs(expr_id, null), at, region);
            },
            .match_ => |match_expr| (try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .{ .at = at }, region)).?,
            .block => |block| (try self.blockExpr(block.statements, block.final_expr, .{ .at = at })).?,
            .if_ => |if_expr| (try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .{ .at = at }, region)).?,
            // A transfer delivers nothing here, and a crash has every type.
            .return_, .break_ => self.ownAs(expr_id, null),
            .crash => |literal| self.bld().crash(at, try self.bld().litStr(self.bodies.text(literal))),
            .run_low_level => |run| blk: {
                if (run.op != .crash or run.args.len != 1) break :blk self.liftTo(try self.ownAs(expr_id, null), at, region);
                break :blk try self.bld().crash(at, try self.exprRef(run.args[0]));
            },
            .lambda, .closure => self.closureAt(expr_id, at),
            .numeral, .str_segment, .str, .binop, .unary_minus, .tuple, .list, .empty_list, .record, .empty_record, .tuple_access, .field_access, .dispatch_call, .type_dispatch_call, .method_eq, .structural_eq, .structural_hash, .dbg, .hosted_lambda, .interpolation, .bytes_literal, .expect, .for_, .code_site, .runtime_error, .expect_err, .ellipsis, .anno_only => self.liftTo(try self.ownAs(expr_id, null), at, region),
        };
    }

    fn exprRefs(self: *Reifier, ids: []const ExprId) Error![]Ref {
        const refs = try self.gpa.alloc(Ref, ids.len);
        errdefer self.gpa.free(refs);
        for (ids, refs) |id, *ref| ref.* = try self.exprRef(id);
        return refs;
    }

    /// The value one expression computes, built in the region being built.
    ///
    /// `as` is the type a nominal hands down to the expression that builds
    /// its backing, the nominal's unfolded backing, where the expression's
    /// own checked type is the nominal itself. A node the checker recorded a
    /// row coercion for is read at the wider tag union the coercion gives it,
    /// where no `as` is handed down (design.md "Row Coercion Primitive").
    fn exprAs(self: *Reifier, expr_id: ExprId, as: ?TyId) Error!Ref {
        const wide = self.bodies.rowCoercion(expr_id) orelse return self.ownAs(expr_id, as);
        const outer_body = self.enter();
        defer self.leave(outer_body);
        const at = as orelse try self.tyOf(wide, self.bodies.expr(expr_id).source_region);
        return self.exprAt(expr_id, at);
    }

    /// The value one expression computes at its own checked type, its row
    /// coercion aside (`exprAs`).
    fn ownAs(self: *Reifier, expr_id: ExprId, as: ?TyId) Error!Ref {
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        const outer_body = self.enter();
        defer self.leave(outer_body);
        const b = self.bld();
        // What this expression builds comes from it (N10); what its parts
        // build comes from them.
        var here = [1]reify.provenance.OriginId{try self.walk.originAt(self.artifact, region)};
        const outer = b.origins;
        b.origins = &here;
        defer b.origins = outer;
        return switch (expr_data.data) {
            .numeral => try self.numeralExpr(expr_id, expr_data.ty, region),
            .str_segment => |literal| try b.litStr(self.bodies.text(literal)),
            // A quoted literal of a custom or open target is its text where
            // its type is `Str`, and otherwise the `from_quote` call the
            // checker wrote: the conversion may parse or validate.
            .str => |segments| blk: {
                const raw = @backingInt(expr_id);
                if (!self.bodies.quoteIsCustom(raw)) break :blk try self.interpolatedExpr(segments);
                const ty = try self.tyOf(expr_data.ty, region);
                if (self.rt().get(ty) == .str) {
                    var text = std.ArrayList(u8).empty;
                    defer text.deinit(self.gpa);
                    try self.bodies.appendText(self.gpa, self.bodies.quoteText(raw), &text);
                    break :blk try b.litStr(text.items);
                }
                if (self.bodies.literalConversionRoot(raw)) |root| try self.walk.noteRead(self.artifact, root);
                break :blk try self.dispatchExpr(self.bodies.quotePlan(raw), expr_data.ty, region);
            },
            .lookup_local => |pattern| try self.lookupRef(pattern, self.bodies.resolvedRef(expr_id), expr_data.ty, expr_id, null, region),
            .match_ => |match_expr| (try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .value, region)).?,
            .block => |block| (try self.blockExpr(block.statements, block.final_expr, .value)).?,
            .if_ => |if_expr| (try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .value, region)).?,
            .binop => |binop| try self.binopExpr(binop.op, binop.lhs, binop.rhs, expr_data.ty, region),
            .unary_minus => |operand| blk: {
                const value = try self.exprRef(operand);
                const owner = self.primitiveOwner(self.bodies.valueType(operand)) orelse
                    break :blk self.rejectError(.unsupported_expression, region, "a negation of this type");
                break :blk try b.primOf(try b.namedPrim(owner, "negate"), &.{value}, try self.tyOf(expr_data.ty, region));
            },
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
            .crash => |literal| try b.crash(try self.tyOf(expr_data.ty, region), try b.litStr(self.bodies.text(literal))),
            // `Type.method(args)` resolves to the same plan a value dispatch
            // leaves behind, and the plan names the dispatcher, so the two
            // are built through one arm.
            .dispatch_call, .type_dispatch_call => try self.dispatchExpr(self.bodies.dispatchPlan(@backingInt(expr_id)), expr_data.ty, region),
            // A hand-written `is_eq` is an ordinary method call; `!=` rides on
            // the plan's result mode, which `dispatchExpr` reads.
            .method_eq => try self.dispatchExpr(self.bodies.dispatchPlan(@backingInt(expr_id)), expr_data.ty, region),
            .structural_eq => |eq| blk: {
                const operand_ty = self.bodies.valueType(eq.lhs);
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
            .tag => |tag_expr| try self.tagExpr(self.bodies.tagLabel(tag_expr.name), tag_expr.args, expr_data.ty, as, region),
            .zero_argument_tag => |tag_expr| try self.tagExpr(self.bodies.tagLabel(tag_expr.name), &.{}, expr_data.ty, as, region),
            .call => |call| try self.callExpr(call.func, call.args, expr_data.ty, null, region),
            .lambda, .closure => try self.closureAt(expr_id, null),
            // A name of another module holds no binding in the scope, so it is
            // the value it was fixed to, or the definition it names.
            .lookup_external, .lookup_required => blk: {
                const reference = self.bodies.resolvedRef(expr_id);
                if (try self.foldedConstant(reference, expr_data.ty, null, region)) |folded| break :blk folded;
                if (reference) |resolved| {
                    if (self.functionOf(expr_data.ty) != null) break :blk try self.functionValue(resolved, null, expr_data.ty, region);
                }
                break :blk self.rejectError(.unsupported_expression, region, exprFormName(expr_data.data));
            },
            // An interpolated literal of the author's own type is the
            // `from_interpolation` call the checker wrote: the method decides
            // what the pieces become.
            .interpolation => |interpolation| try self.interpolationExpr(expr_id, interpolation, expr_data.ty, region),
            // An embedded file, which is the one expression a `List(U8)`
            // literal is written as.
            .bytes_literal => |literal| try b.litBytes(try self.tyOf(expr_data.ty, region), self.bodies.text(literal)),
            // N1j: an assertion for Roc's own test run has no meaning in a
            // target, so it is the `{}` it evaluates to.
            .expect => try b.record(try self.tyOf(expr_data.ty, region), &.{}),
            .return_ => |returned| try self.returnTransfer(returned.expr),
            .break_ => try self.breakTransfer(region),
            .for_ => |loop| blk: {
                try self.forLoop(loop.pattern, loop.expr, loop.body, @backingInt(expr_id), region);
                break :blk try b.record(try self.tyOf(expr_data.ty, region), &.{});
            },
            .code_site => self.rejectCodeValue(region),
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
    fn discard(self: *Reifier, expr_id: ExprId) Error!void {
        // A row-coerced value is built at its coercion, as any value is.
        if (self.bodies.rowCoercion(expr_id) != null) {
            _ = try self.exprRef(expr_id);
            return;
        }
        const expr_data = self.bodies.expr(expr_id);
        const region = expr_data.source_region;
        switch (expr_data.data) {
            .if_ => |if_expr| _ = try self.ifExpr(if_expr.branches, if_expr.final_else, expr_data.ty, .none, region),
            .match_ => |match_expr| _ = try self.matchExpr(match_expr.cond, match_expr.branches, expr_data.ty, .none, region),
            .block => |block| _ = try self.blockExpr(block.statements, block.final_expr, .none),
            .for_ => |loop| try self.forLoop(loop.pattern, loop.expr, loop.body, @backingInt(expr_id), region),
            .expect => {},
            .numeral,
            .code_site,
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
    /// to an iterator over the interpolated values (`iter` on their list), a
    /// `Call` of the row over its captures and the iterator. A `Str` literal
    /// is written once instead (`partsExpr`). The `Err` of the first stage is the crash of a
    /// rejected literal, as the `Err` of a `from_numeral` is
    /// (`convertedWith`), and the rule N13w drops the branches that reach it.
    /// A conversion in the site's cut is one `Prim` over the segments and
    /// the values.
    fn interpolationExpr(self: *Reifier, expr_id: ExprId, interpolation: checked_bodies.InterpolationData, checked_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const raw = @backingInt(expr_id);
        const id = self.bodies.dispatchPlan(raw) orelse return self.rejectError(.unresolved_reference, region, "this literal");
        const plan = self.plans.plans[@backingInt(id)];
        // A `Str` literal is written once, as lowering writes it: the
        // `Str.concat` chain of its parts, and the assembler is not called.
        if (self.builtinNominalOf(plan.dispatcher_ty) == .str) return self.partsExpr(interpolation);
        const b = self.bld();
        const types = self.rt();
        const out_ty = try self.tyOf(checked_ty, region);
        const iter_id = self.bodies.iteratorForPlan(raw) orelse invariant("a checked interpolation has no iterator plan");
        const iter_plan = self.plans.iterator_for_plans[@backingInt(iter_id)];
        // Every segment is kept, the empty ones too: the assembler reads them by position.
        const segments = try self.gpa.alloc(Ref, interpolation.segmentCount());
        defer self.gpa.free(segments);
        for (segments, 0..) |*segment, k| segment.* = try self.exprRef(interpolation.segment(k));
        const values = try self.gpa.alloc(Ref, interpolation.valueCount());
        defer self.gpa.free(values);
        for (values, 0..) |*value, k| value.* = try self.exprRef(interpolation.value(k));
        const segment_list = try b.listOf(try types.listTy(try types.strTy()), segments);
        const value_list = try b.listOf(try self.tyOf(iter_plan.interpolationSite().seed_list_ty, region), values);
        switch (try self.dispatchTarget(DispatchSpec.ofPlan(plan), region, .described)) {
            .definition => |target| {
                if (self.bodies.literalConversionRoot(raw)) |root| try self.walk.noteRead(self.artifact, root);
                self.walk.stage_one += 1;
                defer self.walk.stage_one -= 1;
                const converted = try self.inlineCall(target, &.{segment_list}, null, region);
                // The assembler reads an iterator over the values: `iter` on
                // their list, as lowering builds it.
                const iterator = try self.dispatchWith(.{
                    .method = iter_plan.iter.method,
                    .dispatcher_ty = iter_plan.iter.dispatcher_ty,
                    .resolution = iter_plan.iter.resolution,
                }, &.{value_list}, iter_plan.iterator_ty, region);
                return self.convertedWith(converted, iterator, checked_ty, region);
            },
            // A conversion in the translator's cut is one `Prim` over the
            // segments and the values.
            .foreign => |name| return self.foreignPrim(name, &.{ segment_list, value_list }, out_ty, region),
            .provided, .none => return self.rejectError(.unresolved_reference, region, "a method this literal names no target for"),
        }
    }

    /// A `Str` interpolation's segments and values in order: the `Str.concat`
    /// chain they are (N1e), without the empty segments.
    fn partsExpr(self: *Reifier, interpolation: checked_bodies.InterpolationData) Error!Ref {
        var parts = std.ArrayList(Ref).empty;
        defer parts.deinit(self.gpa);
        for (0..interpolation.segmentCount()) |i| {
            const segment = interpolation.segment(i);
            if (!self.isEmptySegment(segment)) try parts.append(self.gpa, try self.exprRef(segment));
            if (i < interpolation.valueCount()) try parts.append(self.gpa, try self.exprRef(interpolation.value(i)));
        }
        const b = self.bld();
        return switch (parts.items.len) {
            0 => b.litStr(""),
            1 => parts.items[0],
            else => b.call(.str, .concat, parts.items),
        };
    }

    /// A numeric literal: one `Lit` of its type (N1i), or, for a literal of
    /// the author's own type, the `from_numeral` call the checker wrote.
    fn numeralExpr(self: *Reifier, expr_id: ExprId, checked_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const raw = @backingInt(expr_id);
        const primitive = self.builtinNominalOf(checked_ty) orelse {
            if (self.bodies.literalConversionRoot(raw)) |root| try self.walk.noteRead(self.artifact, root);
            return self.dispatchExpr(self.bodies.numeralPlan(raw), checked_ty, region);
        };
        return self.numeralLit(self.bodies.numeralLiteral(raw), primitive, try self.tyOf(checked_ty, region), region);
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
    fn interpolatedExpr(self: *Reifier, segments: []const ExprId) Error!Ref {
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
    fn isEmptySegment(self: *Reifier, expr_id: ExprId) bool {
        const data = self.bodies.exprData(expr_id);
        if (data != .str_segment) return false;
        return self.bodies.text(data.str_segment).len == 0;
    }

    /// A binary operator the checker left as one: `and` and `or` as n-ary
    /// `And` and `Or` (N1c), and an arithmetic or comparison operator as the
    /// builtin of its operands' type.
    fn binopExpr(
        self: *Reifier,
        op: CIR.Expr.Binop.Op,
        lhs_id: ExprId,
        rhs_id: ExprId,
        result_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        switch (op) {
            .@"and", .@"or" => return self.connective(op == .@"and", lhs_id, rhs_id),
            .add, .sub, .mul, .div, .div_trunc, .rem, .lt, .le, .gt, .ge, .eq, .ne => {},
            .range_exclusive, .range_inclusive => return self.rejectError(.unsupported_expression, region, "a range outside a `for`"),
        }
        const owner = self.primitiveOwner(self.bodies.valueType(lhs_id)) orelse
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
    fn connective(self: *Reifier, is_and: bool, lhs_id: ExprId, rhs_id: ExprId) Error!Ref {
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
    fn tupleExpr(self: *Reifier, items: []const ExprId, checked_ty: CheckedTypeId, as: ?TyId, region: base.Region) Error!Ref {
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
        fields: []const CIR.RecordField.Idx,
        ext: ?ExprId,
        unsets: []const CIR.UnsetField.Idx,
        checked_ty: CheckedTypeId,
        as: ?TyId,
        region: base.Region,
    ) Error!Ref {
        const target = as orelse try self.tyOf(checked_ty, region);
        const types = self.rt();
        const shape = switch (types.get(target)) {
            .nominal => try types.unfold(target),
            .record => target,
            .opaque_ => return self.rejectError(.unsupported_type, region, opaque_built),
            .bool_, .str, .int, .float, .dec, .tuple, .tag_union, .list, .func, .recursive => return self.rejectError(.unsupported_type, region, "a record of this type"),
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
        for (fields) |field_id| {
            const field = self.bodies.recordField(field_id);
            const value = try self.exprRef(field.value);
            const index = self.memberIndex(shape, self.names.recordFieldLabelText(field.label)) orelse
                return self.rejectError(.unsupported_type, region, "a field the record's type does not have");
            values[index] = value;
        }
        for (unsets) |unset_id| {
            const label = self.bodies.unsetField(unset_id);
            const index = self.memberIndex(shape, self.names.recordFieldLabelText(label)) orelse
                return self.rejectError(.unsupported_type, region, "a field the record's type does not have");
            std.debug.assert(types.memberSlice(types.get(shape).record)[index].optional);
            unset[index] = true;
        }
        var carried = std.ArrayList(Carry).empty;
        defer carried.deinit(self.gpa);
        if (subject) |from| {
            try self.carryMembers(from, shape, values, unset, &carried, region);
        } else for (values, unset, 0..) |*value, is_unset, index| {
            if (value.* != null or is_unset) continue;
            // No subject: the checker accepts a literal that leaves out an
            // optional field, which is then unset, and one that leaves out
            // a field with a default, which the default fills (Q18).
            const member = self.rt().memberSlice(self.rt().get(shape).record)[index];
            if (member.optional) continue;
            switch (member.default) {
                .none => return self.rejectError(.unsupported_expression, region, "a record literal that leaves out a field"),
                .computed => return self.rejectError(.unsupported_expression, region, "a record literal that leaves out a field whose default is computed. The type does not carry the value of a computed default, so a description cannot fill the field: write the field in the literal"),
                _ => {
                    const field_ty = self.rt().tySlice(member.tys)[0];
                    value.* = try self.valueRef(member.default.value().?, field_ty);
                },
            }
        }
        return self.recordSetting(target, shape, values, carried.items, subject, region);
    }

    /// The literal a field default's value is at the field's type `ty`
    /// (Q18): the nodes the walk builds for the default's literal. The value
    /// was read off the same type, so its shape is the type's.
    fn valueRef(self: *Reifier, value: reify.types.ValueId, ty: TyId) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        const shape = types.get(ty);
        switch (types.value(value)) {
            .int => |v| return b.litInt(ty, v),
            .u128 => |v| return b.litInt(ty, @bitCast(v)),
            .frac => |bits| return switch (shape) {
                .float => |float| switch (float) {
                    .f64 => b.litFloatBits(ty, bits),
                    .f32 => b.litFloatBits(ty, @as(u32, @bitCast(@as(f32, @floatCast(@as(f64, @bitCast(bits))))))),
                },
                .bool_,
                .str,
                .int,
                .dec,
                .record,
                .tuple,
                .tag_union,
                .list,
                .nominal,
                .func,
                .opaque_,
                .recursive,
                => invariant("a float default is at a float type"),
            },
            .dec => |v| return b.litDec(v),
            .bool_ => |v| return b.litBool(v),
            .str => |n| return b.litStr(types.nameText(n)),
            .bytes => |n| return b.litBytes(ty, types.nameText(n)),
            .wrap => |backing| {
                if (shape != .nominal) invariant("a nominal default is at a nominal type");
                const inner = try self.valueRef(backing, try self.rt().unfold(ty));
                return self.bld().wrap(ty, inner);
            },
            .list, .tuple, .record => |span| {
                const items = try self.gpa.dupe(reify.types.ValueId, types.valueSlice(span));
                defer self.gpa.free(items);
                const refs = try self.gpa.alloc(Ref, items.len);
                defer self.gpa.free(refs);
                for (items, refs, 0..) |item, *ref, k| {
                    // Read the type again each time: a part's walk interns types.
                    const t = self.rt();
                    const part_ty = switch (t.get(ty)) {
                        .list => |elem| elem,
                        .tuple => |parts| t.tySlice(parts)[k],
                        .record => |members| t.tySlice(t.memberSlice(members)[k].tys)[0],
                        .bool_,
                        .str,
                        .int,
                        .float,
                        .dec,
                        .tag_union,
                        .nominal,
                        .func,
                        .opaque_,
                        .recursive,
                        => invariant("an aggregate default is at an aggregate type"),
                    };
                    ref.* = try self.valueRef(item, part_ty);
                }
                return switch (types.value(value)) {
                    .list => self.bld().listOf(ty, refs),
                    .tuple => self.bld().tuple(ty, refs),
                    .int,
                    .u128,
                    .frac,
                    .dec,
                    .bool_,
                    .str,
                    .bytes,
                    .record,
                    .tag,
                    .wrap,
                    => self.bld().record(ty, refs),
                };
            },
            .tag => |t| {
                if (shape != .tag_union) invariant("a tag default is at a tag union type");
                const items = try self.gpa.dupe(reify.types.ValueId, types.valueSlice(t.payloads));
                defer self.gpa.free(items);
                const refs = try self.gpa.alloc(Ref, items.len);
                defer self.gpa.free(refs);
                const index = types.memberIndex(ty, t.name) orelse invariant("a tag default names a tag of its union");
                for (items, refs, 0..) |item, *ref, k| {
                    const u = self.rt();
                    ref.* = try self.valueRef(item, u.tySlice(u.memberSlice(u.get(ty).tag_union)[index].tys)[k]);
                }
                return self.bld().tag(ty, t.name, refs);
            },
        }
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
        // `ok` can hold this very `Try` in a cycle, so the type is spelled
        // canonically as a whole (roc-reify-normal-form.md 2.1).
        return types.canonical(try types.nominalTy(try_type_name, .builtin, &.{ ok_ty, err_ty }, backing));
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
        receiver_id: ExprId,
        segments: CIR.Expr.FieldAccessSegment.Span,
        path_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        const b = self.bld();
        const receiver = try self.exprRef(receiver_id);
        const optional = for (0..segments.len) |k| {
            if (self.bodies.fieldAccessSegment(segments, @intCast(k)).mode == .optional) break true;
        } else false;
        if (!optional) {
            var value = receiver;
            for (0..segments.len) |k| {
                const segment = self.bodies.fieldAccessSegment(segments, @intCast(k));
                const record = try self.readable(value);
                value = try b.field(record, try self.fieldIndex(record, self.names.recordFieldLabelText(segment.field_name), segment.source_region));
            }
            return value;
        }
        return self.optionalPath(receiver, segments, 0, try self.tyOf(path_ty, region), region);
    }

    /// The rest of a path that holds an optional segment, from the segment
    /// at `first`, read from `value`, as the `Try` of type `path`.
    fn optionalPath(self: *Reifier, value: Ref, segments: CIR.Expr.FieldAccessSegment.Span, first: u32, path: TyId, region: base.Region) Error!Ref {
        const b = self.bld();
        const types = self.rt();
        var current = value;
        for (first..segments.len) |k| {
            const segment = self.bodies.fieldAccessSegment(segments, @intCast(k));
            const walked: u32 = @intCast(k + 1);
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
                    try self.optionalPath(try b.payload(union_value, ok, 0), segments, walked, path, region)
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
    fn nominalExpr(self: *Reifier, backing_id: ExprId, checked_ty: CheckedTypeId, as: ?TyId, region: base.Region) Error!Ref {
        const target = as orelse try self.tyOf(checked_ty, region);
        return switch (self.rt().get(target)) {
            .nominal => self.bld().wrap(target, try self.exprAs(backing_id, try self.rt().unfold(target))),
            .bool_ => self.exprAs(backing_id, target),
            .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .recursive => self.exprAs(backing_id, target),
            .opaque_ => self.rejectError(.unsupported_type, region, opaque_built),
        };
    }

    /// The refusal of a value of an opaque type built from its fields in a
    /// body the walk reads (1.7). The type hides its fields, and each of its
    /// functions is a primitive (D1), so the fix is to call one.
    const opaque_built = "a value of an opaque type, built from its fields. The type hides its fields from a description: build the value by calling one of the type's functions, which a description names as a primitive";

    /// A tag: a `Bool` literal, or a variant of a tag union, wrapped in the
    /// nominal its type is where it is one.
    fn tagExpr(
        self: *Reifier,
        name: canonical.TagLabelId,
        args: []const ExprId,
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
    fn variantIn(self: *Reifier, union_ty: TyId, name: canonical.TagLabelId, args: []const ExprId, region: base.Region) Error!Ref {
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

    /// `value`, built at its own type, read at `at`, the type a row coercion
    /// gives it (rule L, `roc-reify-tag-names.md` 2.4). A widening is
    /// conformance and adds no node. A lift into a nominal is a `Wrap`. A
    /// lift below a tag payload or a nominal's backing is the `match` that
    /// does it: a `Switch` whose arms construct each tag at the destination.
    /// The steps read only the two types; a pair that is neither a widening
    /// nor a lift is outside the reach of design.md "Row Coercion Primitive".
    fn liftTo(self: *Reifier, value: Ref, at: TyId, region: base.Region) Error!Ref {
        const types = self.rt();
        const own = self.irs().refTy(self.bld().row, value);
        if (try types.widens(own, at)) return value;
        // Both types are closed, and a lift steps only into tag payloads and
        // unfolded backings, so neither is a reference back to a nominal.
        if (types.get(own) == .recursive or types.get(at) == .recursive) invariant("a lift reads a reference back to a nominal around it");
        switch (types.get(at)) {
            .nominal => |target| {
                const backing = try types.unfold(at);
                switch (types.get(own)) {
                    .nominal => |source| {
                        if (source.name != target.name or source.origin != target.origin) invariant("a row coercion reads a nominal at another nominal");
                        return self.liftArms(try self.bld().unwrap(value), backing, at, region);
                    },
                    .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => {},
                }
                if (try types.widens(own, backing)) return self.bld().wrap(at, value);
                if (types.get(own) != .tag_union or types.get(backing) != .tag_union)
                    invariant("a row coercion lifts a value into a nominal whose backing it does not reach");
                return self.liftArms(value, backing, at, region);
            },
            .bool_ => {
                if (types.get(own) != .tag_union) invariant("a row coercion reads a value at Bool that is no tag union");
                return self.liftBool(value, region);
            },
            .tag_union => {
                if (types.get(own) != .tag_union) invariant("a row coercion reads a value at a tag union that is no tag union");
                return self.liftArms(value, at, null, region);
            },
            .str, .int, .float, .dec, .record, .tuple, .list, .func, .opaque_, .recursive => invariant("a row coercion reads a value at a type it neither widens nor lifts to"),
        }
    }

    /// The `match` that lifts the tag union `scrutinee` to the union `union_ty`:
    /// one arm per tag of the scrutinee, each the tag at `union_ty` over its
    /// payloads lifted to the payload types there, in a `Wrap` of `wrap` where
    /// the destination is that nominal.
    fn liftArms(self: *Reifier, scrutinee: Ref, union_ty: TyId, wrap: ?TyId, region: base.Region) Error!Ref {
        const b = self.bld();
        const names = try self.memberNames(self.irs().refTy(b.row, scrutinee), region);
        defer self.gpa.free(names);
        const arms = try self.gpa.alloc(RegionId, names.len);
        defer self.gpa.free(arms);
        for (arms, names) |*arm, name| {
            arm.* = try b.openTagArm(scrutinee, name);
            const types = self.rt();
            const own_ty = self.irs().refTy(b.row, scrutinee);
            const own_count = types.memberSlice(types.get(own_ty).tag_union)[types.memberIndex(own_ty, name).?].tys.len;
            const index = types.memberIndex(union_ty, name) orelse invariant("a row coercion lifts a tag the destination union does not have");
            const target_tys = try self.gpa.dupe(TyId, types.tySlice(types.memberSlice(types.get(union_ty).tag_union)[index].tys));
            defer self.gpa.free(target_tys);
            if (target_tys.len != own_count) invariant("a row coercion lifts a tag to one with another payload count");
            const payloads = try self.gpa.alloc(Ref, target_tys.len);
            defer self.gpa.free(payloads);
            for (payloads, target_tys, 0..) |*payload, target_ty, k| {
                payload.* = try self.liftTo(try b.payload(scrutinee, name, @intCast(k)), target_ty, region);
            }
            const rebuilt = try b.tag(union_ty, name, payloads);
            try b.close(.{ .value = &.{if (wrap) |nominal| try b.wrap(nominal, rebuilt) else rebuilt} });
        }
        return b.switchOn(scrutinee, arms, &.{}, &.{wrap orelse union_ty}, &.{});
    }

    /// The `match` that lifts the tag union `[False, True]`, or a narrower
    /// one, into `Bool`: each arm the literal its tag spells.
    fn liftBool(self: *Reifier, scrutinee: Ref, region: base.Region) Error!Ref {
        const b = self.bld();
        const names = try self.memberNames(self.irs().refTy(b.row, scrutinee), region);
        defer self.gpa.free(names);
        const arms = try self.gpa.alloc(RegionId, names.len);
        defer self.gpa.free(arms);
        const true_name = self.rt().findName("True");
        const false_name = self.rt().findName("False");
        for (arms, names) |*arm, name| {
            arm.* = try b.openTagArm(scrutinee, name);
            const flag = if (name == true_name)
                true
            else if (name == false_name)
                false
            else
                invariant("a row coercion lifts a tag other than False and True into Bool");
            try b.close(.{ .value = &.{try b.litBool(flag)} });
        }
        return b.switchOn(scrutinee, arms, &.{}, &.{try self.rt().boolTy()}, &.{});
    }

    /// The type a `Call` whose own result is `own` is built at, where its
    /// value is read at `at`: `at` where the result widens to it, the
    /// backing where the result widens to the backing of the nominal `at`
    /// (`liftTo` then wraps it), and else the result itself (`liftTo` then
    /// rebuilds it). A `Call` is never built at a nominal its row's result
    /// only lifts into.
    fn liftReach(self: *Reifier, own: TyId, at: TyId) Error!TyId {
        const types = self.rt();
        if (try types.widens(own, at)) return at;
        switch (types.get(at)) {
            .nominal => switch (types.get(own)) {
                .nominal => return own,
                .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => {
                    const backing = try types.unfold(at);
                    return if (try types.widens(own, backing)) backing else own;
                },
            },
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => return own,
        }
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
        pattern_id: PatternId,
        resolved: ?checked.ResolvedValueRefId,
        use_ty: CheckedTypeId,
        use_expr: ?ExprId,
        at: ?TyId,
        region: base.Region,
    ) Error!Ref {
        const binder: BinderId = pattern_id;
        const binding = self.lookupBinding(binder) orelse try self.replayBinding(binder) orelse
            return self.unboundRef(binder, resolved, use_ty, at, region);
        return self.bindingValue(binding, use_ty, use_expr, region);
    }

    /// A reference no scope binds: a constant, or a top-level function used
    /// as a value.
    fn unboundRef(
        self: *Reifier,
        binder: BinderId,
        resolved: ?checked.ResolvedValueRefId,
        use_ty: CheckedTypeId,
        at: ?TyId,
        region: base.Region,
    ) Error!Ref {
        if (try self.foldedConstant(resolved, use_ty, at, region)) |folded| return folded;
        if (resolved) |id| {
            if (self.functionOf(use_ty) != null) return self.functionValue(id, binder, use_ty, region);
            // A parameter whose type a use of a generic function fixes to a
            // function (rule "Function Capture Resolution").
            if (self.value_refs.callableTarget(id).ref == .local_param and self.fixedType(use_ty) != null and
                self.rt().get(try self.tyOf(use_ty, region)) == .func)
            {
                return self.rejectError(.function_parameter, region, self.binderName(binder));
            }
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
    fn inputSlot(self: *Reifier, inputs: *Walk.Inputs, binder: BinderId, region: base.Region) Error!Ref {
        const record = self.bodies.binder(binder);
        if (record.reassignable) return self.rejectError(.input_not_bound, region, "a `var`, whose value at the call is not always the value the description reads");
        if (self.walk.rows.items.len != 1) return self.rejectError(.input_not_bound, region, "a value that a function inside the description reads from around the lambda");
        if (std.debug.runtime_safety) {
            if (inputs.call_leaves) |call_leaves| {
                for (call_leaves) |leaf_binder| {
                    if (leaf_binder == binder) break;
                } else invariant("an input slot reads a binder that is not a leaf of its bound call");
            }
        }
        const pattern = self.bodies.pattern(record.pattern);
        const ty = try self.tyOf(pattern.ty, pattern.source_region);
        const leaf: u32 = for (inputs.leaves.items, 0..) |known, i| {
            if (known == .binder and known.binder == binder) break @intCast(i);
        } else blk: {
            try inputs.leaves.append(self.gpa, .{ .binder = binder });
            break :blk @intCast(inputs.leaves.items.len - 1);
        };
        return self.bld().input(ty, leaf);
    }

    fn bindingValue(self: *Reifier, binding: Binding, use_ty: CheckedTypeId, use_expr: ?ExprId, region: base.Region) Error!Ref {
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
        written_binder: ?BinderId,
        use_ty: CheckedTypeId,
        region: base.Region,
    ) Error!Ref {
        // A top-level value that computes a function is the definition it was
        // written as, built where the name stands, as a constant is.
        if (try self.computedFunction(resolved, region)) |computed| {
            return try computed.written.reader.foldedBody(computed.written.body, null) orelse
                self.rejectError(.unsupported_expression, region, "a top-level constant that computes a function and reads itself");
        }
        return switch (try self.resolvedTarget(resolved, written_binder, region, .described)) {
            .definition => |target| self.closureOf(target, try self.tyOf(use_ty, region)),
            .foreign => |name| if (name.intrinsic)
                self.rejectError(.unsupported_expression, region, "an intrinsic, a function with no Roc body, used as a value")
            else
                self.rejectError(.unsupported_expression, region, "a builtin or a function in the translator's cut used as a value"),
            .provided => self.rejectError(.unsupported_expression, region, "a builtin or a function in the translator's cut used as a value"),
            .value => if (self.value_refs.callableTarget(resolved).ref == .local_param)
                self.rejectError(.function_parameter, region, if (written_binder) |binder| self.binderName(binder) else "")
            else
                self.rejectError(.unsupported_expression, region, "a function value that names no definition"),
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
        body: ExprId,
        /// The top-level definition that binds the constant, and its checked
        /// type in `reader`'s store. Null for a constant the compiler hoisted
        /// out of an expression, which no definition names.
        named: ?struct { def: CIR.Def.Idx, ty: CheckedTypeId },
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
            return .{ .reader = self, .body = body, .named = self.constantNamed(const_ref) };
        }
        const away = self.walk.foreign.findConstant(const_ref) orelse return null;
        const reader = try self.walk.reader(away.module);
        return .{ .reader = reader, .body = away.body, .named = reader.constantNamed(const_ref) };
    }

    /// The definition of this reader's module that binds the constant
    /// `const_ref` names, and its checked type, or null for a hoisted one.
    fn constantNamed(self: *Reifier, const_ref: checked.ConstRef) @FieldType(ConstantDefinition, "named") {
        const pattern = switch (self.const_templates.get(const_ref).owner) {
            .top_level_binding => |binding| binding.pattern,
            .hoisted_root => return null,
        };
        const entry = self.top_level_values.lookupByPattern(pattern) orelse
            invariant("a top-level constant's pattern is a top-level value");
        return .{ .def = entry.def, .ty = self.bodies.pattern(pattern).ty };
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
    ///
    /// A constant that is a primitive (D1), or that the site's cut lists, is
    /// no fold: it is a `Prim` with no arguments, at the type `use_ty` the
    /// name has, and the caller lifts it to `at` as any `Prim` result.
    fn foldedConstant(
        self: *Reifier,
        resolved: ?checked.ResolvedValueRefId,
        use_ty: CheckedTypeId,
        at: ?TyId,
        region: base.Region,
    ) Error!?Ref {
        // An intrinsic constant has no body: it is a `Prim` with no arguments.
        if (resolved) |id| if (try self.intrinsicConstantOf(id)) |intrinsic| {
            const b = self.bld();
            const name = intrinsic.name;
            return try b.primOf(try b.declaredPrim(name.definition, name.owner, name.method, name.intrinsic), &.{}, try self.tyOf(use_ty, region));
        };
        const definition = try self.constantDefinition(resolved) orelse return null;
        if (definition.named) |named| {
            const reader = definition.reader;
            const name: ?ForeignName = if (try reader.primitiveOf(named.def, named.ty)) |primitive| switch (primitive) {
                .operation => |operation| operation,
                // A builtin constant is no primitive: it folds.
                .builtin => invariant("a constant of the builtin module is no primitive"),
            } else self.inCut(reader, definition.body);
            if (name) |prim| {
                const b = self.bld();
                return try b.primOf(try b.declaredPrim(prim.definition, prim.owner, prim.method, prim.intrinsic), &.{}, try self.tyOf(use_ty, region));
            }
        }
        // A computed constant folds to its computation in any package, as a
        // function outside the cut is walked in any package (N8l). A refusal
        // of a `Code` value inside it names the outermost constant (D7).
        const outer_constant = self.walk.constant;
        if (outer_constant == null) {
            if (definition.named) |named| self.walk.constant = definition.reader.constantName(named.def);
        }
        defer self.walk.constant = outer_constant;
        return definition.reader.foldedBody(definition.body, at);
    }

    /// The definition `body` of `reader`'s module, built where a name stands.
    /// Null for a definition that reads itself, which is refused on the repeat
    /// rather than followed forever.
    fn foldedBody(reader: *Reifier, body: ExprId, at: ?TyId) Error!?Ref {
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
        /// The definition, and the reader of the module that wrote it, in
        /// any package (N8l).
        written: struct { reader: *Reifier, body: ExprId },
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
                if (reader.env.module_role == .builtin) {
                    return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides");
                }
                return .{ .written = .{ .reader = reader, .body = away.body } };
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
    fn returnTransfer(self: *Reifier, value_id: ExprId) Error!noreturn {
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

    fn carriedValue(self: *Reifier, binder: BinderId, region: base.Region) Error!Ref {
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

        const Assigned = struct { binder: BinderId, written: ?BinderId };

        fn deinit(s: *Scan) void {
            s.assigned.deinit(s.r.gpa);
        }

        fn scanExprs(s: *Scan, ids: []const ExprId) Allocator.Error!void {
            for (ids) |id| try s.scanExpr(id);
        }

        fn scanExpr(s: *Scan, id: ExprId) Allocator.Error!void {
            const bodies = s.r.bodies;
            switch (bodies.expr(id).data) {
                .numeral,
                .code_site,
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
                    for (m.branches) |branch_id| {
                        const branch = bodies.matchBranch(branch_id);
                        if (branch.guard) |guard| try s.scanExpr(guard);
                        try s.scanExpr(branch.value);
                    }
                },
                .if_ => |i| {
                    for (i.branches) |branch_id| {
                        const branch = bodies.ifBranch(branch_id);
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
                    for (rec.fields) |field| try s.scanExpr(bodies.recordFieldValue(field));
                },
                .block => |block| {
                    for (block.statements) |statement| try s.scanStatement(statement);
                    try s.scanExpr(block.final_expr);
                },
                .tag => |t| try s.scanExprs(t.args),
                .nominal => |n| try s.scanExpr(n.backing_expr),
                .binop => |op| {
                    try s.scanExpr(op.lhs);
                    try s.scanExpr(op.rhs);
                },
                .unary_minus, .dbg => |operand| try s.scanExpr(operand),
                .field_access => |access| try s.scanExpr(access.receiver),
                .tuple_access => |access| try s.scanExpr(access.tuple),
                .dispatch_call, .method_eq, .type_dispatch_call => if (bodies.dispatchPlan(@backingInt(id))) |plan| try s.scanPlan(plan),
                .interpolation => |interpolation| {
                    for (0..interpolation.segmentCount()) |k| try s.scanExpr(interpolation.segment(k));
                    for (0..interpolation.valueCount()) |k| try s.scanExpr(interpolation.value(k));
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
                .generated_numeral, .generated_quote, .literal_pattern_value, .literal_pattern_conversion, .bound_capture_default => {},
            };
        }

        fn scanStatement(s: *Scan, id: StatementId) Allocator.Error!void {
            switch (s.r.bodies.statementData(id)) {
                .decl => |decl| try s.scanExpr(decl.expr),
                .var_ => |decl| try s.scanExpr(decl.expr),
                .reassign => |assignment| {
                    try s.scanExpr(assignment.expr);
                    const written = s.r.binderOf(assignment.pattern);
                    var binders = std.ArrayList(BinderId).empty;
                    defer binders.deinit(s.r.gpa);
                    try s.r.bodies.appendReassignedBinders(s.r.gpa, assignment.pattern, &binders);
                    for (binders.items) |binder| try s.assigned.append(s.r.gpa, .{ .binder = binder, .written = written });
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
                .rejected_method_decl,
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
    fn transfers(self: *Reifier, expr_id: ExprId) bool {
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
        binders: std.ArrayList(BinderId) = .empty,
        aliases: std.ArrayList(Alias) = .empty,

        const Alias = struct { binder: BinderId, index: u32 };

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
            const index = positionOf(BinderId, into.binders.items, a.binder) orelse blk: {
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
    fn branchPlan(self: *Reifier, roots: []const ExprId, want: Want, value_ty: ?TyId) Error!BranchPlan {
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
    fn armCode(self: *Reifier, expr_id: ExprId, want: Want) Error!?Ref {
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
        branches: []const CIR.Expr.IfBranch.Idx,
        final_else: ExprId,
        checked_ty: CheckedTypeId,
        want: Want,
        region: base.Region,
    ) Error!?Ref {
        var roots = std.ArrayList(ExprId).empty;
        defer roots.deinit(self.gpa);
        for (branches) |branch_id| {
            const branch = self.bodies.ifBranch(branch_id);
            try roots.appendSlice(self.gpa, &.{ branch.cond, branch.body });
        }
        try roots.append(self.gpa, final_else);
        var plan = try self.branchPlan(roots.items, want, try self.valueTy(want, checked_ty, region));
        defer plan.deinit(self.gpa);
        var br = Branching.begin(self, &plan);
        return self.ifLevel(&br, branches, final_else, true);
    }

    fn ifLevel(self: *Reifier, br: *Branching, branches: []const CIR.Expr.IfBranch.Idx, final_else: ExprId, top: bool) Error!?Ref {
        const b = self.bld();
        if (branches.len == 0) return self.armBody(br, final_else, top);
        const first = self.bodies.ifBranch(branches[0]);
        const cond = try self.exprRef(first.cond);
        if (b.knownKey(cond)) |key| {
            return if (key == 1) self.armBody(br, first.body, top) else self.ifLevel(br, branches[1..], final_else, top);
        }
        const scope_base = self.scope.items.len;
        var arms: [2]RegionId = undefined;
        arms[0] = try br.openArm(cond, 0);
        try closedArm(self.ifLevel(br, branches[1..], final_else, false));
        self.scope.shrinkRetainingCapacity(scope_base);
        arms[1] = try br.openArm(cond, 1);
        try br.leaf(self.armCode(first.body, br.plan.want), scope_base);
        if (top) return br.finish(cond, &arms, &.{});
        try br.inner(cond, &arms, &.{});
        return null;
    }

    /// The code of one arm: at the construct's top, where every test on the
    /// way was decided, it is built in place; inside an arm, it closes it.
    fn armBody(self: *Reifier, br: *Branching, expr_id: ExprId, top: bool) Error!?Ref {
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
        branches: []const CIR.Expr.Match.Branch.Idx,
        branch: usize,
        alternative: usize,
    };

    /// One pattern and the value it tests.
    const Test = struct { pattern: PatternId, value: Ref };

    /// `match`: a first-match cascade of switches (N1c). Each alternative's
    /// pattern is a queue of tests, left to right; a failing test goes on to
    /// the next alternative, and past the last branch to the crash Roc
    /// lowers the case to.
    fn matchExpr(
        self: *Reifier,
        cond_id: ExprId,
        branches: []const CIR.Expr.Match.Branch.Idx,
        checked_ty: CheckedTypeId,
        want: Want,
        region: base.Region,
    ) Error!?Ref {
        const subject = try self.exprRef(cond_id);
        var roots = std.ArrayList(ExprId).empty;
        defer roots.deinit(self.gpa);
        for (branches) |branch_id| {
            const branch = self.bodies.matchBranch(branch_id);
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
        const branch = self.bodies.matchBranch(at.branches[at.branch]);
        const alternative = self.bodies.matchBranchPattern(branch.patterns[at.alternative]);
        var queue = std.ArrayList(Test).empty;
        defer queue.deinit(self.gpa);
        try queue.append(self.gpa, .{ .pattern = alternative.pattern, .value = subject });
        return self.testQueue(br, subject, at, queue.items, top, region);
    }

    /// Where the cascade goes when the alternative `at` fails.
    fn failed(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, top: bool, region: base.Region) Error!?Ref {
        var next = at;
        if (at.alternative + 1 < self.bodies.matchBranch(at.branches[at.branch]).patterns.len) {
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
        const branch = self.bodies.matchBranch(at.branches[at.branch]);
        const alternative = self.bodies.matchBranchPattern(branch.patterns[at.alternative]);
        // A degenerate alternative binds nothing the branch reads.
        var remaps = std.ArrayList(checked.AlternativeBinderRemap).empty;
        defer remaps.deinit(self.gpa);
        if (!alternative.degenerate) {
            const representative = self.bodies.matchBranchPattern(branch.patterns[0]).pattern;
            try self.bodies.appendAlternativeBinderRemaps(self.gpa, representative, alternative.pattern, &remaps);
        }
        for (remaps.items) |remap| {
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
        value: ExprId,
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
            .assign => {
                try self.bindValue(t.pattern, t.value);
                return self.testQueue(br, subject, at, queue[1..], top, region);
            },
            .underscore => return self.testQueue(br, subject, at, queue[1..], top, region),
            .as => |renamed| {
                try self.bindValue(t.pattern, t.value);
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
                for (destructs) |destruct_id| {
                    const destruct = self.bodies.recordDestruct(destruct_id);
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
            .applied_tag => |applied| return self.tagTest(br, subject, at, queue, self.bodies.tagLabel(applied.name), applied.args, top, region),
            .numeral_literal => {
                if (self.bodies.literalPatternGuard(t.pattern)) |guard| return self.guardedTest(br, subject, at, queue, guard, top, region);
                return self.numeralTest(br, subject, at, queue, self.bodies.numeralLiteral(@backingInt(t.pattern)), top, region);
            },
            .str_literal => |literal| {
                if (self.bodies.literalPatternGuard(t.pattern)) |guard| return self.guardedTest(br, subject, at, queue, guard, top, region);
                const text = try b.litStr(self.bodies.text(literal));
                const eq = try b.call(.str, .is_eq, &.{ try self.readable(t.value), text });
                return self.boolTest(br, subject, at, eq, true, .{ .queue = queue[1..] }, top, region);
            },
            .list => |list| return self.listTest(br, subject, at, queue, list.patterns, list.rest, top, region),
            .str_interpolation => |str| return self.strTest(br, subject, at, queue, str.prefix, str.steps, str.end, top, region),
            .runtime_error => return self.rejectError(.unsupported_expression, pattern.source_region, patternFormName(pattern.data)),
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

    /// A literal pattern of the author's own type: the checker planned the
    /// equality, whose value operand reads the pattern itself as its binder
    /// and whose other operand is the literal converted at the pattern's type.
    fn guardedTest(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, queue: []const Test, guard: checked_bodies.LiteralPatternGuard, top: bool, region: base.Region) Error!?Ref {
        const t = queue[0];
        try self.bindValue(t.pattern, t.value);
        const eq = try self.dispatchExpr(guard.equality_plan, guard.equality_ty, region);
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
        args: []const PatternId,
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
        items: []const PatternId,
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
        items: []const PatternId,
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
        const named_rest: ?PatternId = if (reads.rest) |r| r.pattern else null;
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
        prefix_id: base.StringLiteral.Idx,
        steps: CIR.Pattern.StrPatternStep.Span,
        end: checked.CheckedStrPatternEnd,
        top: bool,
        region: base.Region,
    ) Error!?Ref {
        const b = self.bld();
        const text = try self.readable(queue[0].value);
        const prefix = self.bodies.text(prefix_id);
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
        steps: CIR.Pattern.StrPatternStep.Span,
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
        return self.strSteps(br, subject, at, reads, rest, 0, top);
    }

    /// The steps of a string pattern from the step at `first`, from the text
    /// `rest` that is left.
    fn strSteps(self: *Reifier, br: *Branching, subject: Ref, at: MatchAt, reads: StrReads, rest: Ref, first: u32, top: bool) Error!?Ref {
        const b = self.bld();
        const region = reads.region;
        const captured = reads.captures.items.len;
        defer reads.captures.shrinkRetainingCapacity(captured);
        const step = self.bodies.strPatternStep(reads.steps, first);
        const last = first + 1 == reads.steps.span.len;
        if (last and reads.end == .tail) {
            if (step.capture) |capture| try reads.captures.append(self.gpa, .{ .pattern = capture, .value = rest });
            return self.strDone(br, subject, at, reads, top);
        }
        const str_ty = try self.rt().strTy();
        const pair_ty = try self.rt().recordTy(&.{ .{ .name = "after", .ty = str_ty }, .{ .name = "before", .ty = str_ty } });
        const split_ty = try self.tryOver(pair_ty, "NotFound");
        const split = try b.primOf(try b.namedPrim("Str", "split_first"), &.{ rest, try b.litStr(self.bodies.text(step.delimiter)) }, split_ty);
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
                } else try closedArm(self.strSteps(br, subject, at, reads, after, first + 1, false));
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
    fn blockExpr(self: *Reifier, statements: []const StatementId, final_expr: ExprId, want: Want) Error!?Ref {
        const scope_base = self.scope.items.len;
        for (statements) |statement_id| try self.walkStatement(statement_id);
        const value = try self.armCode(final_expr, want);
        try self.leaveScope(scope_base);
        return value;
    }

    fn walkStatement(self: *Reifier, statement_id: StatementId) Error!void {
        const statement_data = self.bodies.statement(statement_id);
        const region = statement_data.source_region;
        switch (statement_data.data) {
            .decl => |decl| try self.declStatement(decl.pattern, decl.expr),
            // A `var` binds a name the way any other binding does; an
            // assignment after it binds a new version (N3).
            .var_ => |decl| try self.declStatement(decl.pattern, decl.expr),
            .reassign => |assignment| {
                var reassigned = std.ArrayList(BinderId).empty;
                defer reassigned.deinit(self.gpa);
                try self.bodies.appendReassignedBinders(self.gpa, assignment.pattern, &reassigned);
                if (reassigned.items.len != 1) {
                    return self.rejectError(.unsupported_expression, region, "an assignment that writes more than one name");
                }
                // Walked before the new version is bound: `x = x + 1` reads
                // the version it replaces.
                const value = try self.exprRef(assignment.expr);
                const binder = reassigned.items[0];
                try self.bindValue(binder, value);
                // A read after the assignment names whichever of the two
                // binders the checker recorded, so both hold the version.
                if (self.binderOf(assignment.pattern)) |written| {
                    if (written != binder) try self.bindValue(written, value);
                }
            },
            // A written crash in statement position: the rest of the block
            // is what C2 leaves unconstrained, so the crash is a node of
            // its own.
            .crash => |literal| {
                const b = self.bld();
                _ = try b.crash(try self.rt().recordTy(&.{}), try b.litStr(self.bodies.text(literal)));
            },
            .dbg => return self.rejectError(.effect, region, "dbg"),
            .expr => |discarded| try self.discard(discarded),
            // N1j: an assertion for Roc's own test run has no meaning in a
            // target.
            .expect => {},
            .for_ => |loop| try self.forLoop(loop.pattern, loop.expr, loop.body, @backingInt(statement_id), region),
            .while_ => |loop| try self.conditionLoop(loop.cond, loop.body, @backingInt(statement_id), true, region),
            // `while Bool.True { .. }` reaches the walk as one of these two:
            // the body runs until it breaks or returns.
            .infinite_loop, .breakable_loop => |loop| try self.conditionLoop(loop.cond, loop.body, @backingInt(statement_id), false, region),
            .break_ => try self.breakTransfer(region),
            .return_ => |returned| try self.returnTransfer(returned.expr),
            // A promoted local function evaluates nothing where it is
            // written. Every use of its name resolves to its procedure, which
            // the walk reads as a definition of the module. The declaration
            // of a method checking rejected evaluates nothing either.
            .promoted_proc, .rejected_method_decl => {},
            // A type-level statement names a type for the checker and leaves
            // no value behind.
            .import_,
            .alias_decl,
            .where_alias_decl,
            .nominal_decl,
            .type_anno,
            .type_var_alias,
            => {},
            .var_uninitialized,
            .runtime_error,
            => return self.rejectError(.unsupported_expression, region, statementFormName(statement_data.data)),
        }
    }

    /// `pattern = value`. A binding that holds a function is held rather
    /// than built: a call on it names its row, and a read builds a closure
    /// of it.
    fn declStatement(self: *Reifier, pattern_id: PatternId, value_id: ExprId) Error!void {
        const region = self.bodies.pattern(pattern_id).source_region;
        if (self.functionOf(self.bodies.valueType(value_id)) != null) {
            return self.bindName(pattern_id, .{ .function = value_id }, region);
        }
        if (self.bodies.patternData(pattern_id) == .underscore) return self.discard(value_id);
        try self.bindPattern(pattern_id, try self.exprRef(value_id));
    }

    // Loops //

    /// The `var`s a loop carries, by the binders the loop `loop_node` (a `for`
    /// expression or a loop statement) reassigns, in their order, with the
    /// other binders a scan of the body finds each read under.
    fn loopCarried(self: *Reifier, loop_node: u32, roots: []const ExprId, into: *Carried) Error!void {
        var s: Scan = .{ .r = self };
        defer s.deinit();
        for (roots) |root| try s.scanExpr(root);
        for (try self.bodies.loopMutationBinders(loop_node)) |binder| {
            const binding = self.lookupBinding(binder) orelse continue;
            if (binding.kind != .value) continue;
            if (positionOf(BinderId, into.binders.items, binder) != null) continue;
            try into.binders.append(self.gpa, binder);
        }
        for (s.assigned.items) |a| {
            const written = a.written orelse continue;
            if (written == a.binder) continue;
            const index = positionOf(BinderId, into.binders.items, a.binder) orelse continue;
            try into.aliases.append(self.gpa, .{ .binder = written, .index = @intCast(index) });
        }
    }

    /// `for pattern in iterable { body }`: a `ForRange` over a builtin
    /// integer range, a `ForList` over a list, and a `Loop` over the
    /// iterator protocol otherwise (N11a to N11c).
    fn forLoop(
        self: *Reifier,
        pattern_id: PatternId,
        iterable_id: ExprId,
        body_id: ExprId,
        /// The `for` expression or statement, which holds the loop's
        /// iterator plan and its reassigned binders.
        loop_node: u32,
        region: base.Region,
    ) Error!void {
        var carried: Carried = .{};
        defer carried.deinit(self.gpa);
        try self.loopCarried(loop_node, &.{body_id}, &carried);
        if (try self.rangeOf(iterable_id)) |range| {
            const start = try self.exprRef(range.start);
            const end = try self.exprRef(range.end);
            return self.countedLoop(.{ .range = .{ .inclusive = range.inclusive, .start = start, .end = end } }, pattern_id, body_id, &carried, region);
        }
        const iterable_ty = self.bodies.valueType(iterable_id);
        if (self.builtinNominalOf(iterable_ty) == .list) {
            const list = try self.exprRef(iterable_id);
            return self.countedLoop(.{ .list = list }, pattern_id, body_id, &carried, region);
        }
        const plan = self.plans.iterator_for_plans[
            @backingInt(self.bodies.iteratorForPlan(loop_node) orelse
                return self.rejectError(.unresolved_reference, region, "this for loop"))
        ];
        try self.iteratorLoop(plan, pattern_id, body_id, &carried, region);
    }

    /// The bounds of a range a `for` walks, where the iterable is a range
    /// method of a builtin integer.
    const Range = struct { inclusive: bool, start: ExprId, end: ExprId };

    fn rangeOf(self: *Reifier, iterable_id: ExprId) Error!?Range {
        if (self.bodies.exprData(iterable_id) != .dispatch_call) return null;
        const plan_id = self.bodies.dispatchPlan(@backingInt(iterable_id)) orelse return null;
        const plan = self.plans.plans[@backingInt(plan_id)];
        const inclusive = self.ranges.inclusiveOf(plan.method) orelse return null;
        const primitive = self.builtinNominalOf(plan.dispatcher_ty) orelse return null;
        if (intTarget(primitive) == null) return null;
        const operands = plan.argsSlice(self.plans);
        if (operands.len != 2) return null;
        const start = switch (operands[0]) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments, .literal_pattern_value, .literal_pattern_conversion, .bound_capture_default => return null,
        };
        const end = switch (operands[1]) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments, .literal_pattern_value, .literal_pattern_conversion, .bound_capture_default => return null,
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
    fn countedLoop(self: *Reifier, counted: Counted, pattern_id: PatternId, body_id: ExprId, carried: *const Carried, region: base.Region) Error!void {
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
            .range => |range| try b.noteRangeLoop(body, range.start, range.end, range.inclusive),
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
        cond: ExprId,
        /// A general loop: the iterator protocol's step.
        step: struct { plan: static_dispatch.IteratorForPlan, pattern: PatternId },
        /// A loop that runs until it breaks.
        none,
    };

    /// Build a loop body, which `loop.body` is and which is open: bind the
    /// slots, walk the turn, and end it in `Continue` with the next slots.
    fn loopBody(self: *Reifier, loop: Loop, carried: *const Carried, body_id: ExprId, entry: Entry, region: base.Region) Error!void {
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

    fn turn(self: *Reifier, loop: Loop, body_id: ExprId, entry: Entry, region: base.Region) Error!void {
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
    fn continueTurn(self: *Reifier, loop: Loop, body_id: ExprId, iterator: ?Ref, region: base.Region) Error!void {
        try self.discard(body_id);
        const next = try self.slotValues(loop, iterator, region);
        defer self.gpa.free(next);
        try self.terminate(.{ .continue_ = next });
    }

    /// `while cond { body }`: a `Bool` switch on the condition at the top of
    /// the turn, whose `False` arm breaks with the slots as they stand.
    fn whileTurn(self: *Reifier, loop: Loop, cond_id: ExprId, body_id: ExprId, region: base.Region) Error!void {
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
    fn stepTurn(self: *Reifier, loop: Loop, plan: static_dispatch.IteratorForPlan, pattern_id: PatternId, body_id: ExprId, region: base.Region) Error!void {
        const b = self.bld();
        const iterator = Ref.regionParam(loop.body, loop.slot_base);
        const step = try self.readable(try self.dispatchWith(.{
            .method = plan.next.method,
            .dispatcher_ty = plan.next.dispatcher_ty,
            .resolution = plan.next.resolution,
        }, &.{iterator}, plan.forLoopSite().step_ty, region));
        const step_ty = self.irs().refTy(b.row, step);
        const topology = plan.forLoopSite().step_topology;
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

    fn itemTurn(self: *Reifier, loop: Loop, pattern_id: PatternId, item: Ref, body_id: ExprId, rest: Ref, region: base.Region) Error!void {
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
    fn iteratorLoop(self: *Reifier, plan: static_dispatch.IteratorForPlan, pattern_id: PatternId, body_id: ExprId, carried: *const Carried, region: base.Region) Error!void {
        const b = self.bld();
        const operands = plan.iter.argsSlice(self.plans);
        const iter_args = try self.gpa.alloc(Ref, operands.len);
        defer self.gpa.free(iter_args);
        for (operands, iter_args) |operand, *arg| arg.* = switch (operand) {
            .checked_expr => |child| try self.exprRef(child),
            .loop_iterator_state => invariant("iter reads the loop's iterator before the loop"),
            .interpolation_seed, .interpolation_iterator, .interpolation_value => invariant("a for loop's iter reads an interpolation operand"),
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
    fn conditionLoop(self: *Reifier, cond_id: ExprId, body_id: ExprId, loop_node: u32, tests: bool, region: base.Region) Error!void {
        const b = self.bld();
        var carried: Carried = .{};
        defer carried.deinit(self.gpa);
        try self.loopCarried(loop_node, &.{ cond_id, body_id }, &carried);
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

    /// A function in the site's cut, or a method of an opaque nominal, named
    /// by owner and method (N8h). The owner of a function in the cut is the
    /// nominal it is an associated item of, or its module where it is none.
    /// `definition` is what identifies it: two packages can give two
    /// functions one name (F2).
    pub const ForeignName = struct {
        owner: []const u8,
        method: []const u8,
        definition: reify.ir.Definition,
        /// Its `where` requirements and what the call recorded for them (D7).
        evidence: PrimEvidence = .{},
        /// Whether it is an intrinsic, which has no body. Only a refusal
        /// reads it: the `Prim` of an intrinsic is the `Prim` of any other
        /// function.
        intrinsic: bool = false,
    };

    /// The `where` requirements of a primitive a call names, and what the
    /// call recorded for them (D7). `scheme` holds the evidence params of
    /// the primitive's template, in its scheme's requirement order with a
    /// constraint alias expanded, and `names` the reader of the module whose
    /// names they are in. `recorded` is null where the call recorded nothing.
    /// `receiver` is set where the compiler's own derivation reached the
    /// primitive, which records nothing by construction: the receiver's type
    /// fixes each requirement's dispatcher (`receiverEvidence`).
    const PrimEvidence = struct {
        names: ?*Reifier = null,
        template: ?checked.CheckedProcedureTemplate = null,
        scheme: []const static_dispatch.EvidenceParamRecord = &.{},
        recorded: ?Recorded = null,
        receiver: ?FramedType = null,

        /// The requirements of the template `template` of `reader`'s module.
        fn of(reader: *Reifier, template: checked.CheckedProcedureTemplate) PrimEvidence {
            return .{ .names = reader, .template = template, .scheme = reader.procedure_templates.evidenceParams(&template) };
        }
    };

    /// What a call recorded for its callee's `where` requirements: the
    /// entries, in the callee scheme's requirement order, the reader of the
    /// module that recorded them, and the evidence the walk held there,
    /// which an entry that forwards reads (`supply`).
    const Recorded = struct {
        reader: *Reifier,
        entries: []const static_dispatch.CheckedEvidence,
        scope: SuppliedEvidence,
    };

    /// What identifies a function in a site's cut: the module that defines it
    /// and its checked body, which is what every path to a callee resolves it
    /// to (`resolvedTarget`, `methodTargetCallee`), and what a row is keyed by.
    pub const CutKey = struct { artifact: [32]u8, body: ExprId };

    /// A function or a constant a `code_primitives` item, or a translator
    /// call, names: the reader of the module that defines it, its body, its
    /// definition, and its checked type in that reader's store.
    const CutMember = struct { reader: *Reifier, body: ExprId, def: CIR.Def.Idx, ty: CheckedTypeId };

    /// The function a resolved reference names, where it names one defined
    /// as a lambda, following every exact alias (`same = add_one`), or null
    /// for any other reference: a local, a constant, a value that computes a
    /// function, a function the host or the platform provides.
    fn cutMember(self: *Reifier, resolved: checked.ResolvedValueRefId) Allocator.Error!?CutMember {
        const use = switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc => |use| use,
            .promoted_top_level_proc,
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
                std.debug.assert(std.meta.eql(top_level.artifact.bytes, self.artifact.bytes));
                switch (self.procedure_bindings.get(top_level.binding).body) {
                    .direct_template => |direct| {
                        const template_ref = switch (direct.template) {
                            .checked => |template| template,
                            .lifted, .synthetic => return null,
                        };
                        const template = self.procedure_templates.templates.items[@backingInt(template_ref.template)];
                        const body_id = switch (template.body) {
                            .checked_body => |body| body,
                            .intrinsic_wrapper, .entry_wrapper => return null,
                            // The walk never asks for an intrinsic's body.
                            .unimplemented => {
                                std.debug.assert(!self.templateIsIntrinsic(template));
                                return null;
                            },
                        };
                        const def = self.names.procBase(template.proc_base).source_def_idx orelse return null;
                        return .{ .reader = self, .body = body_id, .def = @fromBackingInt(def), .ty = template.checked_fn_root };
                    },
                    .callable_eval_template => |id| {
                        const lookup = self.callable_eval_templates.templates[@backingInt(id)].forwarded_lookup orelse return null;
                        const forwarded = self.value_refs.lookupIdByExpr(lookup) orelse
                            invariant("an alias forwards to a lookup with no resolved reference");
                        return self.cutMember(forwarded);
                    },
                    .checked_error => return null,
                }
            },
            .imported => |imported| {
                if (self.walk.foreign.findExported(imported.artifact, imported.def)) |definition| {
                    const reader = try self.walk.reader(definition.module);
                    return .{ .reader = reader, .body = definition.body, .def = imported.def, .ty = definition.template.checked_fn_root };
                }
                const alias = self.walk.foreign.findExportedAlias(imported.artifact, imported.def) orelse return null;
                const reader = try self.walk.reader(alias.module);
                const forwarded = reader.value_refs.lookupIdByExpr(alias.lookup) orelse
                    invariant("an alias forwards to a lookup with no resolved reference");
                return reader.cutMember(forwarded);
            },
            .hosted, .platform_required => return null,
        }
    }

    /// What a `code_primitives` entry names: a function, as `cutMember`
    /// resolves it, or a top-level constant, or null for anything else.
    fn listedMember(self: *Reifier, resolved: checked.ResolvedValueRefId) Allocator.Error!?CutMember {
        if (try self.cutMember(resolved)) |function| return function;
        const constant = try self.constantDefinition(resolved) orelse return null;
        const named = constant.named orelse return null;
        return .{ .reader = constant.reader, .body = constant.body, .def = named.def, .ty = named.ty };
    }

    /// The function a translator call names: the reader of the module that
    /// defines it, and its definition.
    const Translator = struct { reader: *Reifier, def: CIR.Def.Idx };

    /// The function a translator call names, as a member of a cut is named:
    /// the callee of a direct call, through its resolved reference, or the
    /// method a method call dispatches to, through its dispatch plan. Null
    /// where the call names no function defined as a lambda or intrinsic.
    fn translatorFunction(self: *Reifier, call: ExprId) Allocator.Error!?Translator {
        switch (self.bodies.expr(call).data) {
            .call => |direct| {
                const resolved = self.lookupResolved(direct.func) orelse return null;
                if (try self.listedIntrinsic(resolved)) |intrinsic| return .{ .reader = intrinsic.reader, .def = intrinsic.def };
                const member = try self.cutMember(resolved) orelse return null;
                return .{ .reader = member.reader, .def = member.def };
            },
            .dispatch_call => {
                // A dispatch checking rejected has no plan, and the build
                // already stops at its error.
                const id = self.bodies.dispatchPlan(@backingInt(call)) orelse return null;
                const node_id = switch (self.plans.plans[@backingInt(id)].resolution) {
                    .direct_closed, .direct_parametric => |direct| direct.evidence,
                    .direct_pending => |node_id| node_id,
                    .checked_error, .@"unreachable" => return null,
                    // The checker plans a method call's arguments against the
                    // method's parameters only once its receiver's type is
                    // known, so a site's translator is dispatched directly.
                    .evidence_dependent, .structural => invariant("a translator's method call dispatches to a target its receiver's type names"),
                };
                return self.methodTranslator(self.plans.evidenceNode(node_id).target);
            },
            // A call checking rejected, which the build stops at.
            .runtime_error => return null,
            .numeral,
            .code_site,
            .str_segment,
            .str,
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
            .field_access,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
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
            => invariant("a translator call is a direct call or a method call"),
        }
    }

    /// The function one method target names, as a translator is named, or
    /// null for a method that is no function of a module the walk reads: a
    /// builtin, whose type declares no cut, a local function, a derived one.
    fn methodTranslator(self: *Reifier, target: static_dispatch.MethodTarget) Allocator.Error!?Translator {
        const procedure = switch (target.kind) {
            .procedure => |procedure| procedure,
            // A method bound to a computed callable has no definition the
            // walk reads as a translator.
            .local_proc, .structural, .callable_binding => return null,
        };
        const def = try self.methodTargetDef(procedure, target) orelse return null;
        if (try self.intrinsicOfTemplate(procedure.template.artifact, def)) |intrinsic| return .{ .reader = intrinsic.reader, .def = intrinsic.def };
        const found = self.methodDefinition(procedure.template, def) orelse return null;
        return switch (found) {
            .here => .{ .reader = self, .def = def },
            .away => |definition| .{ .reader = try self.walk.reader(definition.module), .def = def },
            .here_builtin, .provided => null,
        };
    }

    /// The resolved reference a checked lookup holds, or null for an
    /// expression that is no lookup.
    fn lookupResolved(self: *Reifier, expr_id: ExprId) ?checked.ResolvedValueRefId {
        return switch (self.bodies.exprData(expr_id)) {
            .lookup_local, .lookup_external => self.bodies.resolvedRef(expr_id),
            .numeral,
            .code_site,
            .str_segment,
            .str,
            .bytes_literal,
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

    /// The nominal this module declares that has `def` as an associated
    /// item, and the item's name, or null for a definition that is none.
    fn ownerOf(self: *Reifier, def: CIR.Def.Idx) ?struct { decl: CIR.Statement.Idx, method: base.Ident.Idx } {
        for (self.env.method_defs.entries.items) |entry| {
            if (entry.value.def_idx != def) continue;
            if (self.env.store.getStatement(entry.key.owner) != .s_nominal_decl) continue;
            return .{ .decl = entry.key.owner, .method = entry.key.methodIdent() };
        }
        return null;
    }

    /// The qualified name of the definition `def` of this module (N8h): the
    /// nominal it is an associated item of and the item, `Glsl.Vec3` and
    /// `scale`, or the module and the definition where it is no item.
    /// The name a top-level constant binds, or null for a definition whose
    /// pattern binds no single name.
    fn constantName(self: *Reifier, def: CIR.Def.Idx) ?[]const u8 {
        return switch (self.env.store.getPattern(self.env.store.getDef(def).pattern)) {
            .assign => |assign| self.env.getIdentText(assign.ident),
            .var_assign,
            .as,
            .applied_tag,
            .nominal,
            .nominal_external,
            .deferred_import_ref,
            .record_destructure,
            .list,
            .tuple,
            .num_literal,
            .small_dec_literal,
            .dec_literal,
            .frac_f32_literal,
            .frac_f64_literal,
            .num_from_numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => null,
        };
    }

    fn qualifiedName(self: *Reifier, def: CIR.Def.Idx) ForeignName {
        const definition: reify.ir.Definition = .{ .module = self.artifact.bytes, .def = @backingInt(def) };
        if (self.ownerOf(def)) |owned| {
            const header = self.env.store.getStatement(owned.decl).s_nominal_decl.header;
            return .{
                .owner = self.env.getIdentText(self.env.store.getTypeHeader(header).name),
                .method = self.env.getIdentText(owned.method),
                .definition = definition,
            };
        }
        const ident = switch (self.env.store.getPattern(self.env.store.getDef(def).pattern)) {
            .assign => |assign| assign.ident,
            .var_assign,
            .as,
            .applied_tag,
            .nominal,
            .nominal_external,
            .deferred_import_ref,
            .record_destructure,
            .list,
            .tuple,
            .num_literal,
            .small_dec_literal,
            .dec_literal,
            .frac_f32_literal,
            .frac_f64_literal,
            .num_from_numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => invariant("a function defined as a lambda binds one name"),
        };
        return .{ .owner = self.env.module_name, .method = self.env.getIdentText(ident), .definition = definition };
    }

    /// What a definition is to every description, whichever path reaches it
    /// (D1, `roc-reify-opaque-proposal.md` 3.1). `self` is the reader of the
    /// module that defines it, and `ty` its checked type in that reader's
    /// store.
    const Primitive = union(enum) {
        /// A function of the builtin module, named by its export name, which
        /// the path that reached it reads from the procedure's template.
        builtin,
        /// An operation of an opaque type, named by its qualified name.
        operation: ForeignName,
    };

    /// An intrinsic a description names (`AnnotationOnlyKind.intrinsic`): an
    /// annotated declaration with no body outside the builtin and platform
    /// modules. It is a `Prim` at every site, whatever the site's cut says,
    /// and the walk never asks for its body. `reader` is the reader of the
    /// module that declares it, `name` its qualified name, marked as an
    /// intrinsic, and `template` its procedure template, whose `where`
    /// requirements its `Prim` carries, or null for a constant.
    const Intrinsic = struct {
        reader: *Reifier,
        def: CIR.Def.Idx,
        name: ForeignName,
        template: ?checked.CheckedProcedureTemplate,

        /// Its `where` requirements, which the call answers (D7).
        fn requirements(self: Intrinsic) PrimEvidence {
            return if (self.template) |template| PrimEvidence.of(self.reader, template) else .{};
        }
    };

    /// Whether `env` declares `def` as an intrinsic.
    fn defIsIntrinsic(env: *const ModuleEnv, def: CIR.Def.Idx) bool {
        const expr = env.store.getExpr(env.store.getDef(def).expr);
        if (expr != .e_anno_only) return false;
        return expr.e_anno_only.kind == .intrinsic;
    }

    /// Whether this reader's procedure template `template` is an intrinsic's.
    fn templateIsIntrinsic(self: *Reifier, template: checked.CheckedProcedureTemplate) bool {
        const def = self.names.procBase(template.proc_base).source_def_idx orelse return false;
        return defIsIntrinsic(self.env, @fromBackingInt(def));
    }

    /// The intrinsic `def` of this reader's module, or null where `def` is no
    /// intrinsic.
    fn intrinsicAt(self: *Reifier, def: CIR.Def.Idx) ?Intrinsic {
        if (!defIsIntrinsic(self.env, def)) return null;
        var name = self.qualifiedName(def);
        name.intrinsic = true;
        const template: ?checked.CheckedProcedureTemplate = if (self.procedure_templates.lookupByDef(def)) |ref|
            self.procedure_templates.get(ref.template)
        else
            null;
        // An annotation with no body publishes no checked body.
        if (template) |found| std.debug.assert(found.body == .unimplemented);
        return .{ .reader = self, .def = def, .name = name, .template = template };
    }

    /// The intrinsic `def` of the module whose artifact is `artifact`, or null
    /// where `def` is no intrinsic or the walk cannot read that module.
    fn intrinsicOfTemplate(self: *Reifier, artifact: canonical.ArtifactRef, def: CIR.Def.Idx) Allocator.Error!?Intrinsic {
        if (std.meta.eql(artifact.bytes, self.artifact.bytes)) return self.intrinsicAt(def);
        const module = self.walk.foreign.findModule(&artifact.bytes) orelse return null;
        if (!defIsIntrinsic(module.env(), def)) return null;
        return (try self.walk.reader(module)).intrinsicAt(def);
    }

    /// The intrinsic a procedure binding names, or null for a binding of any
    /// other procedure.
    fn intrinsicCallee(self: *Reifier, binding: checked.ProcedureBindingRef) Allocator.Error!?Intrinsic {
        switch (binding) {
            .top_level => |top_level| {
                if (!std.meta.eql(top_level.artifact.bytes, self.artifact.bytes)) return null;
                const template_ref = switch (self.procedure_bindings.get(top_level.binding).body) {
                    .direct_template => |direct| switch (direct.template) {
                        .checked => |template| template,
                        .lifted, .synthetic => return null,
                    },
                    .callable_eval_template, .checked_error => return null,
                };
                const template = self.procedure_templates.templates.items[@backingInt(template_ref.template)];
                if (template.body != .unimplemented) return null;
                const def = self.names.procBase(template.proc_base).source_def_idx orelse return null;
                return self.intrinsicAt(@fromBackingInt(def));
            },
            .imported => |imported| return self.intrinsicOfTemplate(imported.artifact, imported.def),
            .hosted, .platform_required => return null,
        }
    }

    /// The intrinsic constant `const_ref` names, or null for any other
    /// constant.
    fn intrinsicConstant(self: *Reifier, const_ref: checked.ConstRef) Allocator.Error!?Intrinsic {
        const reader = if (std.meta.eql(const_ref.artifact.bytes, self.artifact.bytes)) self else blk: {
            const module = self.walk.foreign.findModule(&const_ref.artifact.bytes) orelse return null;
            break :blk try self.walk.reader(module);
        };
        if (reader.const_templates.get(const_ref).state != .unimplemented) return null;
        const named = reader.constantNamed(const_ref) orelse return null;
        return reader.intrinsicAt(named.def);
    }

    /// The intrinsic constant a resolved reference names, or null for a
    /// reference to anything else.
    fn intrinsicConstantOf(self: *Reifier, resolved: checked.ResolvedValueRefId) Allocator.Error!?Intrinsic {
        return switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_const, .imported_const => |use| self.intrinsicConstant(use.const_ref),
            .top_level_proc,
            .imported_proc,
            .promoted_top_level_proc,
            .selected_hoisted_const,
            .local_proc,
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .hosted_proc,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            => null,
        };
    }

    /// The intrinsic a resolved reference names, a function or a constant,
    /// or null for a reference to anything else.
    fn listedIntrinsic(self: *Reifier, resolved: checked.ResolvedValueRefId) Allocator.Error!?Intrinsic {
        return switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| self.intrinsicCallee(use.binding),
            .top_level_const, .imported_const => |use| self.intrinsicConstant(use.const_ref),
            .selected_hoisted_const,
            .local_proc,
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .hosted_proc,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            => null,
        };
    }

    /// The builtin module declares its primitives by being the builtin
    /// module: each of its functions is one, and a constant folds. A module
    /// that declares a nominal with `::` declares its primitives by the rule
    /// of D1: each function or constant it defines whose checked type
    /// mentions such a nominal at any depth. Every other definition is none,
    /// and the walk reads its body. The rule reads only the declaration's
    /// opaque flag, the nominal's builtin origin, the module that declares
    /// it and the definition's checked type.
    ///
    /// An intrinsic is classified first: it has no body, so it is a primitive
    /// whatever its type mentions, named by its qualified name. Its `Prim` is
    /// the `Prim` of any other function.
    fn primitiveOf(self: *Reifier, def: CIR.Def.Idx, ty: CheckedTypeId) Allocator.Error!?Primitive {
        if (self.intrinsicAt(def)) |intrinsic| return .{ .operation = intrinsic.name };
        if (self.env.module_role == .builtin) return if (self.functionOf(ty) != null) .builtin else null;
        // A value site computes its literal through the bodies of an opaque
        // type's operations (`Walk.opaque_backings`).
        if (self.walk.opaque_backings) return null;
        const here_hash = self.env.contentIdentityHash() orelse
            invariant("a module the walk reads has its content identity");
        // A nominal names the module that declares it by an identity of this
        // module's name store. When the store has no identity for this
        // module, no nominal of the checked types is declared by it.
        const here = self.names.lookupModuleIdentity(here_hash) orelse return null;
        var seen: collections.DenseMapUnmanaged(CheckedTypeId, void) = .empty;
        defer seen.deinit(self.gpa);
        if (!try self.mentionsOpaqueOf(&seen, here, ty)) return null;
        return .{ .operation = self.qualifiedName(def) };
    }

    /// Whether `id` mentions, at any depth, a nominal declared with `::` by
    /// the module whose module identity is `module`: through a function's
    /// parameters and result, a record's fields, a tag's payloads, a
    /// nominal's arguments and a `where` requirement's method type. A
    /// nominal's backing is not descended, as the walk does not descend it.
    fn mentionsOpaqueOf(self: *Reifier, seen: *collections.DenseMapUnmanaged(CheckedTypeId, void), module: canonical.ModuleIdentityId, id: CheckedTypeId) Allocator.Error!bool {
        if ((try seen.getOrPut(self.gpa, id)).found_existing) return false;
        switch (self.types.payload(id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| return self.mentionsOpaqueOf(seen, module, alias.backing),
            .function => |fn_ty| {
                for (fn_ty.args) |arg| if (try self.mentionsOpaqueOf(seen, module, arg)) return true;
                return self.mentionsOpaqueOf(seen, module, fn_ty.ret);
            },
            .nominal => |nominal| {
                if (nominal.is_opaque and nominal.builtin == null and
                    nominal.origin_module == module) return true;
                for (nominal.args) |arg| if (try self.mentionsOpaqueOf(seen, module, arg)) return true;
                return false;
            },
            .tuple => |parts| {
                for (parts) |part| if (try self.mentionsOpaqueOf(seen, module, part)) return true;
                return false;
            },
            .record => |record| {
                var fields = record.fields.iterator();
                while (fields.next()) |field| if (try self.mentionsOpaqueOf(seen, module, field.ty)) return true;
                return self.mentionsOpaqueOf(seen, module, record.ext);
            },
            .tag_union => |union_ty| {
                var tags = union_ty.tags.iterator();
                while (tags.next()) |variant| {
                    for (variant.args) |arg| if (try self.mentionsOpaqueOf(seen, module, arg)) return true;
                }
                return self.mentionsOpaqueOf(seen, module, union_ty.ext);
            },
            .flex, .rigid => |variable| {
                var constraints = variable.constraints.iterator();
                while (constraints.next()) |constraint| if (try self.mentionsOpaqueOf(seen, module, constraint.fn_ty)) return true;

                return false;
            },
            .empty_record, .empty_tag_union, .pending, .err => return false,
        }
    }

    /// The function in the site's cut that a callee resolved to `reader` and
    /// `body` is, named, or null where the callee is no such function.
    fn inCut(self: *Reifier, reader: *Reifier, body: ExprId) ?ForeignName {
        return self.walk.cut.get(.{ .artifact = reader.artifact.bytes, .body = body });
    }

    /// A plain call, `f(x)`: `Call` of the callee's row, a `Prim` for a
    /// builtin or a function in the site's cut, or the derived codec or
    /// curried definition the call runs, folded into one node.
    fn callExpr(
        self: *Reifier,
        func: ExprId,
        operands: []const ExprId,
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
            // A primitive's `where` evidence is the call's own: the callee
            // reference is the instantiation edge the checker keyed it by
            // (D7).
            .provided => |found| {
                var provided = found;
                provided.evidence.recorded = self.callRecorded(func);
                const args = try self.exprRefs(operands);
                defer self.gpa.free(args);
                return self.providedPrim(provided, args, result_ty, region);
            },
            .foreign => |found| {
                var name = found;
                name.evidence.recorded = self.callRecorded(func);
                const args = try self.exprRefs(operands);
                defer self.gpa.free(args);
                return self.foreignPrim(name, args, try self.tyOf(result_ty, region), region);
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
        for (target.captures) |capture_id| {
            const capture = owner.bodies.capture(capture_id);
            if (capturedCallee(target.bound, capture.pattern) != null) continue;

            const pattern = owner.bodies.pattern(capture.pattern);
            const outer_body = owner.enter();
            defer owner.leave(outer_body);
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
        exprs: []const ExprId,
    };

    /// A builtin by its export name, `Builtin.Num.I64.plus`: the `Prim` of
    /// its owner and method (N1a).
    fn providedPrim(self: *Reifier, provided: Provided, args: []const Ref, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        return self.providedPrimAt(provided, args, try self.tyOf(result_ty, region), region);
    }

    /// `providedPrim`, of the type `ty`.
    fn providedPrimAt(self: *Reifier, provided: Provided, args: []const Ref, ty: TyId, region: base.Region) Error!Ref {
        const id = try self.providedId(provided, region);
        const evidence = try self.primEvidence(provided.evidence, region);
        defer self.gpa.free(evidence);
        return self.bld().primWith(id, args, ty, evidence);
    }

    fn providedId(self: *Reifier, provided: Provided, region: base.Region) Error!ir.PrimId {
        const name = prims.namedOfExport(provided.name) orelse
            return self.rejectError(.unresolved_reference, region, "a builtin with no owner in its name");
        return self.bld().namedPrimWithRole(name.owner, name.method, provided.role);
    }

    /// An operation of an opaque type or a function in the site's cut
    /// (N8h), with the evidence of its call (D7), of the type `ty`.
    fn foreignPrim(self: *Reifier, name: ForeignName, args: []const Ref, ty: TyId, region: base.Region) Error!Ref {
        const b = self.bld();
        const id = try b.declaredPrim(name.definition, name.owner, name.method, name.intrinsic);
        const evidence = try self.primEvidence(name.evidence, region);
        defer self.gpa.free(evidence);
        return b.primWith(id, args, ty, evidence);
    }

    /// What the call whose callee reference is `func` recorded for the
    /// callee's `where` requirements, or null where it recorded nothing.
    fn callRecorded(self: *Reifier, func: ExprId) ?Recorded {
        const entries = self.plans.siteEvidence(func) orelse return null;
        return .{ .reader = self, .entries = entries, .scope = self.evidence };
    }

    /// The refusal of a primitive call whose `where` evidence the checker
    /// left to a later stage: the walk does not guess the answer (D7).
    const unrecorded_evidence = "a call whose `where` evidence the compiler did not record";

    /// The evidence of a call of a primitive (D7), as `ir.EvidenceWords`
    /// reads it: for each `where` requirement of the primitive's scheme, in
    /// the scheme's order, the method the checker chose at the call. Empty
    /// for a primitive with no requirement. The caller frees it.
    fn primEvidence(self: *Reifier, evidence: PrimEvidence, region: base.Region) Error![]u32 {
        if (evidence.scheme.len == 0) return &.{};
        var words: std.ArrayList(u32) = .empty;
        errdefer words.deinit(self.gpa);
        try self.evidenceEntries(&words, evidence, region);
        return words.toOwnedSlice(self.gpa);
    }

    /// The count of `evidence`'s requirements, then one entry for each
    /// (`ir.EvidenceWords`). Each entry reads only what the checker
    /// recorded: a target it names is classified as a callee is (D1), a
    /// derivation is `derived`, and an obligation no value reaches is
    /// `unreachable_`. An answer left to a later stage is refused. Where the
    /// compiler's own derivation reached the primitive, the checker records
    /// nothing by construction, and the receiver answers (`receiverEvidence`).
    fn evidenceEntries(self: *Reifier, words: *std.ArrayList(u32), evidence: PrimEvidence, region: base.Region) Error!void {
        try words.append(self.gpa, @intCast(evidence.scheme.len));
        if (evidence.scheme.len == 0) return;
        const recorded = evidence.recorded orelse {
            const receiver = evidence.receiver orelse return self.rejectError(.unsupported_expression, region, unrecorded_evidence);
            return self.receiverEvidence(words, evidence, receiver, region);
        };
        // The checker records one entry per requirement, in its order.
        std.debug.assert(recorded.entries.len == evidence.scheme.len);
        const names = evidence.names.?;
        for (evidence.scheme, recorded.entries) |param, entry| {
            const method = try self.rt().name(names.names.methodNameText(param.method));
            // The type the requirement dispatches on, where the call fixed it.
            const ty = try recorded.reader.tyOf(entry.dispatcher_ty, region);
            try words.appendSlice(self.gpa, &.{ method.index(), ty.index() });
            var supplied = recorded.reader.suppliedEntry(entry, recorded.scope);
            var shared = false;
            if (supplied.evidence.resolution == .constraint) {
                if (sharedTarget(supplied.evidence.resolution.constraint, recorded.scope)) |slot| {
                    supplied = slot;
                    shared = true;
                }
            }
            switch (supplied.evidence.resolution) {
                .direct => |node_id| {
                    const node = supplied.reader.plans.evidenceNode(node_id);
                    const edge: DispatchEdge = .{ .reader = supplied.reader, .node = node, .scope = supplied.scope };
                    // A shared slot's target is related to the use's own
                    // callable, not to the slot's edge. That callable's first
                    // parameter is the dispatcher, so the receiver fixes the
                    // target's instance (`receiverInstantiation`), and a
                    // variable only the rest of the callable fixes is refused.
                    const fixing: MethodFixing = if (shared)
                        .{ .receiver = recorded.reader.resolvedType(entry.dispatcher_ty) }
                    else
                        .{ .edge = edge };
                    const callee = try self.methodTargetCallee(supplied.reader, node.target, fixing, region, .described);
                    try self.calleeEvidence(words, callee, shared, region);
                },
                .structural => try words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.derived), method.index() }),
                .unreachable_value => try words.append(self.gpa, @backingInt(ir.EvidenceKind.unreachable_)),
                // An entry that forwards to evidence no enclosing call of the
                // walk supplied, or whose answer the checker derives later.
                .constraint, .from_callable, .from_scheme => return self.rejectError(.unsupported_expression, region, unrecorded_evidence),
                .checked_error => invariant("a site the checker rejected reached the walk"),
            }
        }
    }

    /// The target part of one entry for the callee a requirement resolved
    /// to: a primitive with its own entries, or a row of the site, built at
    /// the evidence's instance as any callee is. `shared` says the entry is
    /// a slot `sharedTarget` named, whose target has no requirement of its
    /// own.
    fn calleeEvidence(self: *Reifier, words: *std.ArrayList(u32), callee: DispatchCallee, shared: bool, region: base.Region) Error!void {
        switch (callee) {
            .provided => |provided| {
                std.debug.assert(!shared or provided.evidence.scheme.len == 0);
                try words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.prim), (try self.providedId(provided, region)).index() });
                try self.evidenceEntries(words, provided.evidence, region);
            },
            .foreign => |name| {
                std.debug.assert(!shared or name.evidence.scheme.len == 0);
                const id = try self.bld().declaredPrim(name.definition, name.owner, name.method, name.intrinsic);
                try words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.prim), id.index() });
                try self.evidenceEntries(words, name.evidence, region);
            },
            .definition => |target| {
                const row = try self.calledRow(target);
                try words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.row), row.index() });
            },
            .none => return self.rejectError(.unresolved_reference, region, "a method this call names no target for"),
        }
    }

    /// The refusals of a requirement a derivation reached that the receiver
    /// does not answer by the checker's rule (`receiverEntry`).
    const receiver_composite = "a `where` requirement on a composite type, reached by a derivation";
    const receiver_variable = "a `where` requirement on a type variable, reached by a derivation";
    const receiver_undeclared = "a `where` requirement whose method no module in reach declares, reached by a derivation";
    const receiver_structural = "a `where` requirement on a structural type that permits no derived equality or hash, reached by a derivation";

    /// The entries of `evidence` where the compiler's own derivation reached
    /// the primitive (a derived `==` reaching `List.is_eq`): it planned no
    /// call, so the checker recorded nothing, by construction. The receiver
    /// fixes the template's quantified variables (`receiverInstantiation`),
    /// so each requirement's dispatcher is the variable its `slot` names,
    /// and `receiverEntry` resolves it.
    fn receiverEvidence(self: *Reifier, words: *std.ArrayList(u32), evidence: PrimEvidence, receiver: FramedType, region: base.Region) Error!void {
        const names = evidence.names.?;
        const template = evidence.template.?;
        var instance = (try names.receiverInstantiation(template, receiver, region)) orelse
            invariant("a primitive with a `where` requirement has no quantified variable");
        defer instance.substitution.deinit(self.gpa);
        const scheme_vars = names.schemeVars(template);
        for (evidence.scheme) |param| {
            const text = names.names.methodNameText(param.method);
            const method = try self.rt().name(text);
            const slot = param.slot orelse return self.rejectError(.unsupported_expression, region, receiver_composite);
            // `receiverInstantiation` binds every quantified variable or refuses.
            const dispatcher = instance.substitution.get(scheme_vars[slot]) orelse
                invariant("a receiver instantiation left a quantified variable unbound");
            const ty = try dispatcher.reader.tyOfIn(dispatcher.frame, dispatcher.id, region);
            try words.appendSlice(self.gpa, &.{ method.index(), ty.index() });
            try self.receiverEntry(words, param, text, method, dispatcher, region);
        }
    }

    /// The target part of one entry `receiverEvidence` reads, by the rule the
    /// checker applies to a dispatcher of that type (checked_artifact.zig
    /// `resolveObligationStep`), which Monotype applies to the same
    /// derivation's components (monotype/lower.zig
    /// `synthesizeComponentEvidenceAtNodeForPurpose`):
    ///
    /// | Dispatcher | Entry |
    /// |---|---|
    /// | nominal, registry target is a procedure | that target, as `dispatchTarget` reads a derivation's dispatch |
    /// | nominal, registry target is structural | `derived` |
    /// | record, tuple, tag union, `{}`, function | `derived`, where the requirement permits a derived equality or hash |
    ///
    /// Anything else is refused by name: a nominal no registry in reach
    /// declares the method for, a type variable, and a structural type whose
    /// requirement is a codec or a map (Monotype then reads inhabitedness,
    /// which the walk does not).
    fn receiverEntry(
        self: *Reifier,
        words: *std.ArrayList(u32),
        param: static_dispatch.EvidenceParamRecord,
        text: []const u8,
        method: NameId,
        dispatcher: FramedType,
        region: base.Region,
    ) Error!void {
        const reader = dispatcher.reader;
        switch (reader.types.payload(dispatcher.id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| return self.receiverEntry(words, param, text, method, reader.resolvedTypeIn(dispatcher.frame, alias.backing), region),
            .nominal => {
                const target = receiverMethod(dispatcher, text) orelse
                    return self.rejectError(.unsupported_type, region, receiver_undeclared);
                if (std.meta.activeTag(target.kind) == .structural) {
                    return words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.derived), method.index() });
                }
                const callee = try reader.methodTargetCallee(reader, target, .{ .receiver = dispatcher }, region, .described);
                return self.calleeEvidence(words, callee, false, region);
            },
            .record, .tuple, .tag_union, .empty_record, .empty_tag_union, .function => {
                const kind = param.structural orelse return self.rejectError(.unsupported_type, region, receiver_structural);
                return switch (static_dispatch.unpinnedDispatchResolution(kind)) {
                    .structural => words.appendSlice(self.gpa, &.{ @backingInt(ir.EvidenceKind.derived), method.index() }),
                    .unreachable_value => self.rejectError(.unsupported_type, region, receiver_structural),
                };
            },
            .flex, .rigid => return self.rejectError(.unresolved_type, region, receiver_variable),
            .pending, .err => return self.rejectError(.unresolved_type, region, "an unresolved type"),
        }
    }

    /// The entry of `scope` a forwarded requirement names where the use
    /// relates the slot's target to its own callable (`independent_callable`),
    /// and the slot's entry is the whole answer: the checker shares the
    /// slot's target identity with the use. A target with no requirement of
    /// its own (no nested evidence), a derivation and an unreachable
    /// obligation are then the whole answer. A walked target's row is built
    /// at the instance the use's own callable fixes, which no table records:
    /// the caller reads it off the dispatcher, the callable's first
    /// parameter (`receiverInstantiation`), and refuses a target with a
    /// variable only the rest of the callable fixes. Null for any other
    /// entry, which the caller refuses.
    fn sharedTarget(forwarded: static_dispatch.ConstraintEvidenceRef, scope: SuppliedEvidence) ?SuppliedEntry {
        if (!forwarded.independent_callable or forwarded.index.depth != 0) return null;
        if (forwarded.index.index >= scope.entries.len) return null;
        const slot = scope.entries[forwarded.index.index];
        return switch (slot.evidence.resolution) {
            .direct => |node_id| switch (slot.reader.plans.evidenceNode(node_id).nested) {
                .resolved => |nested| if (nested.len == 0) slot else null,
                .from_callable, .through_alias => null,
            },
            .structural, .unreachable_value => slot,
            .constraint, .from_callable, .from_scheme, .checked_error => null,
        };
    }

    /// `name`, carrying the `where` requirements `evidence` of its call.
    fn withEvidence(name: ForeignName, evidence: PrimEvidence) ForeignName {
        var out = name;
        out.evidence = evidence;
        return out;
    }

    /// The expression that constructed a function, and the reader of the
    /// module that wrote it.
    const Constructor = struct {
        reader: *Reifier,
        expr: ExprId,
    };

    /// The call one expression constructed a function with: the call itself,
    /// the one a held binding remembers, or the definition of a top-level
    /// value that computes the function. A name the root reads from the block
    /// around it is replayed first, as `calleeTarget` replays it, so
    /// `pred = above(n)` and then `pred(x)` is the call `above(n)(x)`.
    fn constructorCall(self: *Reifier, func: ExprId, region: base.Region) Error!?Constructor {
        const callee = self.bodies.expr(func);
        switch (callee.data) {
            .lookup_local => |binder| {
                const binding = self.lookupBinding(binder) orelse try self.replayBinding(binder) orelse
                    return self.computedConstructor(self.bodies.resolvedRef(func), region);
                return switch (binding.kind) {
                    .function => |bound| if (self.lambdaOf(bound) == null) .{ .reader = self, .expr = bound } else null,
                    .value, .constant, .callee => null,
                };
            },
            .lookup_external, .lookup_required => return self.computedConstructor(self.bodies.resolvedRef(func), region),
            .numeral,
            .code_site,
            .str_segment,
            .str,
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
        const written = computed.written;
        // A value written as another such value, `renamed = doubler`, is the
        // one it names. The definition is marked while the walk follows it, so
        // a value that reaches itself ends at its own definition.
        const data = written.reader.bodies.exprData(written.body);
        const named: ?checked.ResolvedValueRefId = if (data == .lookup_local or data == .lookup_external or data == .lookup_required)
            written.reader.bodies.resolvedRef(written.body)
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
    fn curriedCall(self: *Reifier, func: ExprId, operands: []const ExprId, at: TyId, region: base.Region) Error!?Ref {
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
        const id = writer.bodies.dispatchPlan(@backingInt(constructor.expr)) orelse return null;
        const plan = writer.plans.plans[@backingInt(id)];
        const found = try writer.dispatchTarget(DispatchSpec.ofPlan(plan), region, .described);
        const callee = switch (found) {
            .definition => |target| target,
            // A builtin or a function in the site's cut carries no body to
            // flatten a curried call through.
            .provided, .foreign, .none => return null,
        };
        const constructed = try writer.dispatchExprs(plan, region);
        defer self.gpa.free(constructed);
        return self.flattenedCall(callee, .{ .reader = writer, .exprs = constructed }, operands, at);
    }

    /// One `Call` over both argument groups, against the row that gathers
    /// both lambdas' parameters. Takes the callee's instantiation either way.
    fn flattenedCall(self: *Reifier, callee: CalleeTarget, constructed: ArgumentGroup, operands: []const ExprId, at: TyId) Error!?Ref {
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
    fn dispatchExprs(self: *Reifier, plan: static_dispatch.StaticDispatchCallPlan, region: base.Region) Error![]ExprId {
        const operands = plan.argsSlice(self.plans);
        const ids = try self.gpa.alloc(ExprId, operands.len);
        errdefer self.gpa.free(ids);
        for (operands, ids) |operand, *id| id.* = switch (operand) {
            .checked_expr => |child| child,
            .generated_numeral, .generated_quote, .generated_interpolation_segments => return self.rejectError(.unsupported_expression, region, "a compiler-generated argument"),
            .literal_pattern_value,
            .literal_pattern_conversion,
            .bound_capture_default,
            => invariant("a call's dispatch plan passes no literal pattern or bound capture operand"),
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
    fn bindCallees(self: *Reifier, target: *CalleeTarget, operands: []const ExprId, region: base.Region) Error!void {
        // A lifted lambda arrives with the names it captured already bound.
        var bound = std.ArrayList(BoundCallee).fromOwnedSlice(target.bound);
        target.bound = &.{};
        errdefer {
            self.releaseBound(bound.items);
            bound.deinit(self.gpa);
        }
        const before = bound.items.len;
        for (operands, 0..) |operand, index| {
            if (self.functionOf(self.bodies.valueType(operand)) == null) continue;
            const passed = try self.passedArgument(operand, region) orelse continue;
            try bound.append(self.gpa, .{ .param = .{ .position = @intCast(index) }, .target = passed });
        }
        if (bound.items.len != before) target.key.callees = boundCalleesKey(bound.items);
        target.bound = try bound.toOwnedSlice(self.gpa);
    }

    /// The definition one function argument names: a name the caller wrote,
    /// or the row a lambda written at the site lifts into. A template's
    /// argument must name one.
    fn passedCallee(self: *Reifier, operand: ExprId, region: base.Region) Error!CalleeTarget {
        if (self.lambdaOf(operand) != null and self.capturesOf(operand).len != 0) {
            return self.rejectError(.capture, region, self.capturedName(self.bodies.capture(self.capturesOf(operand)[0]).pattern));
        }
        return try self.passedArgument(operand, region) orelse
            self.rejectError(.unsupported_expression, region, "a function value that names no definition");
    }

    /// The definition one function argument of a call names, or null for a
    /// function the call passes as a value: a lambda that captures, or one
    /// that names no definition.
    fn passedArgument(self: *Reifier, operand: ExprId, region: base.Region) Error!?CalleeTarget {
        if (self.lambdaOf(operand) != null) {
            // A lambda that captures only names a call fixed captures no
            // value: it is the definitions those names stand for.
            const captures = self.capturesOf(operand);
            for (captures) |capture| {
                if (self.calleeInScope(self.bodies.capture(capture).pattern) == null) return null;
            }
            return try self.enclosedLambda(operand, null, captures);
        }
        return switch (try self.calleeTarget(operand, region)) {
            .definition => |definition| definition,
            .value => null,
            .provided, .foreign => self.rejectError(.unsupported_expression, region, "a builtin or a function in the translator's cut, passed as an argument"),
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
    fn keptOperands(self: *Reifier, operands: []const ExprId, bound: []const BoundCallee) Allocator.Error![]ExprId {
        var kept = std.ArrayList(ExprId).empty;
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
    fn calleeTarget(self: *Reifier, func: ExprId, region: base.Region) Error!Callee {
        const callee = self.bodies.expr(func);
        if (callee.data == .lookup_local) {
            const binder = callee.data.lookup_local;
            if (self.lookupBinding(binder)) |binding| return self.liftedTarget(binding, callee.ty, func, region);
            if (try self.replayBinding(binder)) |binding| return self.liftedTarget(binding, callee.ty, func, region);
            const resolved = self.bodies.resolvedRef(func) orelse
                return self.rejectError(.unresolved_reference, region, "this call");
            return self.resolvedTarget(resolved, binder, region, .described);
        }
        const resolved = switch (callee.data) {
            .lookup_external, .lookup_required => self.bodies.resolvedRef(func) orelse
                return self.rejectError(.unresolved_reference, region, "this call"),
            .numeral,
            .code_site,
            .str_segment,
            .str,
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
        return self.resolvedTarget(resolved, null, region, .described);
    }

    /// The definition a use of a template names (D1): a lookup of a
    /// procedure, or a dispatch whose plan names its target. What the use
    /// fixes the template's variables to is read in this reader's frame, and
    /// what it supplies for the template's `where` obligations is composed
    /// with this reader's evidence, as a call's is. Null for a use that names
    /// no definition the walk builds a row for. A primitive with an
    /// inventory (a method of a `::` type) is that definition here, as
    /// `usedTemplate` reads it (`CalleeUse.instance_table`).
    fn useTarget(self: *Reifier, use: ExprId, region: base.Region) Error!?CalleeTarget {
        if (try self.usedConstant(use)) |constant| return try self.constantTarget(constant, region);
        switch (self.bodies.expr(use).data) {
            .lookup_local => |binder| {
                const resolved = self.bodies.resolvedRef(use) orelse return null;
                const callee = try self.resolvedTarget(resolved, binder, region, .instance_table);
                var target = switch (callee) {
                    .definition => |target| target,
                    .provided, .foreign, .value => return null,
                };
                if (self.plans.siteEvidence(use)) |supplied| target.evidence = try self.supply(supplied, self.evidence);
                return target;
            },
            .lookup_external => {
                const resolved = self.bodies.resolvedRef(use) orelse return null;

                const callee = try self.resolvedTarget(resolved, null, region, .instance_table);
                var target = switch (callee) {
                    .definition => |target| target,
                    .provided, .foreign, .value => return null,
                };
                if (self.plans.siteEvidence(use)) |supplied| target.evidence = try self.supply(supplied, self.evidence);
                return target;
            },
            .numeral,
            .code_site,
            .str_segment,
            .str,
            .bytes_literal,
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
            => {
                const spec = (try self.dispatchOfUse(use)) orelse return null;
                return switch (try self.dispatchTarget(spec, region, .instance_table)) {
                    .definition => |target| target,
                    .provided, .foreign, .none => null,
                };
            },
        }
    }

    /// The template a use names (D1), without what it fixes: the reader of
    /// the module that defines it, its template id and its body. Null for a
    /// use that names no procedure of a module the walk reads, or where the
    /// reference does not resolve; such a use has no inventory.
    fn usedTemplate(self: *Reifier, use: ExprId) Allocator.Error!?UsedTemplate {
        const outer_rejection = self.walk.rejection;
        defer self.walk.rejection = outer_rejection;
        return self.usedTemplateOrRefused(use) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.Rejected, error.Diverged => null,
        };
    }

    const UsedTemplate = struct {
        reader: *Reifier,
        template: canonical.CheckedProcedureTemplateId,
        body: ExprId,
    };

    /// A constant a use reads, which evaluation computes at each type a use
    /// fixes (Q16), or a top-level binding that computes a function, which
    /// its entry wrapper computes the same way: the reader of its module,
    /// the entry template its evaluation runs, which holds its inventory,
    /// its body, and the type the use fixes, or null where the use fixes
    /// none.
    const UsedConstant = struct {
        reader: *Reifier,
        template: canonical.CheckedProcedureTemplateId,
        body: ExprId,
        requested: ?CheckedTypeId,
    };

    fn usedConstant(self: *Reifier, use: ExprId) Allocator.Error!?UsedConstant {
        switch (self.bodies.expr(use).data) {
            .lookup_local, .lookup_external => {},
            .numeral,
            .code_site,
            .str_segment,
            .str,
            .bytes_literal,
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
            => return null,
        }
        const resolved = self.lookupResolved(use) orelse return null;
        const const_use = switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_const, .imported_const => |const_use| const_use,
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |proc_use| return self.usedComputed(proc_use),
            .local_param,
            .local_value,
            .local_mutable_version,
            .pattern_binder,
            .local_proc,
            .selected_hoisted_const,
            .hosted_proc,
            .platform_required_declaration,
            .platform_required_checked_error,
            .platform_required_const,
            .platform_required_proc,
            => return null,
        };
        const reader = if (std.meta.eql(const_use.const_ref.artifact.bytes, self.artifact.bytes)) self else blk: {
            const away = self.walk.foreign.findConstant(const_use.const_ref) orelse return null;
            break :blk try self.walk.reader(away.module);
        };
        const eval = switch (reader.const_templates.get(const_use.const_ref).state) {
            .eval_template => |eval| eval,
            .stored_const, .reserved, .unimplemented => return null,
        };
        if (!std.meta.eql(eval.entry_template.artifact.bytes, reader.artifact.bytes)) invariant("a constant's entry template is in another module");
        return .{
            .reader = reader,
            .template = eval.entry_template.template,
            .body = reader.const_bodies.get(eval.body).body_expr,
            .requested = const_use.requested_source_ty_payload,
        };
    }

    /// A top-level binding that computes a function, as `usedConstant`
    /// reads it: its entry wrapper runs its body at each type a use fixes,
    /// so the wrapper's template holds the inventory of the body. Null for
    /// any other procedure; an exact alias forwards to the procedure its
    /// lookup names.
    fn usedComputed(self: *Reifier, use: checked.ProcedureUseTemplate) Allocator.Error!?UsedConstant {
        const reader: *Reifier, const template_id: checked.CallableEvalTemplateId = switch (use.binding) {
            .top_level => |top_level| blk: {
                if (!std.meta.eql(top_level.artifact.bytes, self.artifact.bytes)) return null;
                break :blk .{ self, switch (self.procedure_bindings.get(top_level.binding).body) {
                    .callable_eval_template => |id| id,
                    .direct_template, .checked_error => return null,
                } };
            },
            .imported => |imported| blk: {
                const away = self.walk.foreign.findExportedComputed(imported.artifact, imported.def) orelse return null;
                break :blk .{ try self.walk.reader(away.module), away.template };
            },
            .hosted, .platform_required => return null,
        };
        const template = reader.callable_eval_templates.templates[@backingInt(template_id)];
        if (template.forwarded_lookup != null) return null;
        const wrapper = reader.entry_wrappers.lookupByRoot(template.root) orelse
            invariant("a binding that computes a function has no entry wrapper");
        std.debug.assert(std.meta.eql(wrapper.template.artifact.bytes, reader.artifact.bytes));
        return .{
            .reader = reader,
            .template = wrapper.template.template,
            .body = template.body,
            .requested = use.source_fn_ty_payload,
        };
    }

    /// What a use of a constant fixes the variables of its entry template
    /// to: the template's scheme, at the value the template returns, read
    /// together with the type the use requests.
    fn constantTarget(self: *Reifier, constant: UsedConstant, region: base.Region) Error!CalleeTarget {
        const reader = constant.reader;
        const requested = constant.requested orelse invariant("a constant use an inventory names fixes no type");
        const template = reader.procedure_templates.templates.items[@backingInt(constant.template)];
        const value_ty = switch (reader.types.payload(template.checked_fn_root)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .function => |function| function.ret,
            .pending,
            .err,
            .flex,
            .rigid,
            .alias,
            .record,
            .tuple,
            .nominal,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => invariant("a constant's entry template is no function"),
        };
        const instance = try reader.instantiationOf(.{ .vars = reader.schemeVars(template), .root = value_ty }, self, requested, null, region, .call);
        return .{
            .key = .{
                .artifact = reader.artifact.bytes,
                .body = constant.body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .reader = reader,
            .instantiation = instance,
        };
    }

    fn usedTemplateOrRefused(self: *Reifier, use: ExprId) Error!?UsedTemplate {
        const region = self.bodies.expr(use).source_region;
        switch (self.bodies.expr(use).data) {
            .lookup_local, .lookup_external => {
                if (try self.usedConstant(use)) |constant| return .{ .reader = constant.reader, .template = constant.template, .body = constant.body };
                const resolved = self.lookupResolved(use) orelse return null;
                const target = switch (self.value_refs.callableTarget(resolved).ref) {
                    .top_level_proc, .imported_proc, .promoted_top_level_proc => |target| target,
                    .local_param,
                    .local_value,
                    .local_mutable_version,
                    .pattern_binder,
                    .local_proc,
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
                // A procedure of a module the walk does not read (a builtin,
                // the host, the platform) has no inventory.
                switch (target.binding) {
                    .top_level => {},
                    .imported => |imported| if (self.walk.foreign.findExported(imported.artifact, imported.def) == null and
                        self.walk.foreign.findExportedAlias(imported.artifact, imported.def) == null) return null,
                    .hosted, .platform_required => return null,
                }
                const written_binder: ?BinderId = switch (self.bodies.expr(use).data) {
                    .lookup_local => |pattern| pattern,
                    .numeral,
                    .code_site,
                    .str_segment,
                    .str,
                    .bytes_literal,
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
                // An intrinsic has no body, so it has no inventory.
                if (try self.intrinsicCallee(target.binding) != null) return null;
                const reached = try self.reachedProcedure(target.binding, written_binder, region);
                return .{ .reader = reached.reader, .template = reached.template.template_id, .body = reached.body };
            },
            .numeral,
            .code_site,
            .str_segment,
            .str,
            .bytes_literal,
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
            => {
                const spec = (try self.dispatchOfUse(use)) orelse return null;
                const direct = switch (spec.resolution) {
                    .direct_closed, .direct_parametric => |direct| direct,
                    .direct_pending, .evidence_dependent, .structural, .checked_error, .@"unreachable" => return null,
                };
                const node = self.plans.evidenceNode(direct.evidence);
                const procedure = switch (node.target.kind) {
                    .procedure => |procedure| procedure,
                    .callable_binding => |binding| return try self.computedMethod(binding),
                    .local_proc, .structural => return null,
                };
                const def = try self.methodTargetDef(procedure, node.target) orelse return null;
                // An intrinsic has no body, so it has no inventory.
                if (try self.intrinsicOfTemplate(procedure.template.artifact, def) != null) return null;
                const found = self.methodDefinition(procedure.template, def) orelse return null;
                const reader = switch (found) {
                    .provided => return null,
                    .here, .here_builtin => self,
                    .away => |definition| try self.walk.reader(definition.module),
                };
                return .{ .reader = reader, .template = found.template().template_id, .body = found.body() };
            },
        }
    }

    /// Whether `type_id` mentions a variable of `vars`: a variable is a
    /// flex or rigid type id, and it is read where it stands, through
    /// records (with the kind variable of an undetermined field), tag unions,
    /// tuples, functions, aliases and a nominal's arguments.
    fn mentionsAny(self: *Reifier, type_id: CheckedTypeId, vars: *const RowVars) Allocator.Error!bool {
        if (vars.count() == 0) return false;
        var seen: RowVars = .empty;
        defer seen.deinit(self.gpa);
        return self.mentionsIn(type_id, vars, &seen);
    }

    /// Every flex or rigid variable `type_id` mentions, read as `mentionsIn`
    /// reads them.
    fn collectVars(self: *Reifier, type_id: CheckedTypeId, out: *RowVars) Allocator.Error!void {
        var seen: RowVars = .empty;
        defer seen.deinit(self.gpa);
        var work = std.ArrayList(CheckedTypeId).empty;
        defer work.deinit(self.gpa);
        try work.append(self.gpa, type_id);
        while (work.pop()) |id| {
            if ((try seen.getOrPut(self.gpa, id)).found_existing) continue;
            switch (self.types.payload(id)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .flex, .rigid => |variable| {
                    try out.put(self.gpa, id, {});
                    var constraints = variable.constraints.iterator();
                    while (constraints.next()) |constraint| try work.append(self.gpa, constraint.fn_ty);
                },
                .alias => |alias| try work.append(self.gpa, alias.backing),
                .function => |fn_ty| {
                    try work.appendSlice(self.gpa, fn_ty.args);
                    try work.append(self.gpa, fn_ty.ret);
                },
                .nominal => |nominal| try work.appendSlice(self.gpa, nominal.args),
                .tuple => |parts| try work.appendSlice(self.gpa, parts),
                .record => |record| {
                    var fields = record.fields.iterator();
                    while (fields.next()) |field| {
                        if (field.kind.undeterminedVariable()) |kind| try work.append(self.gpa, kind);
                        try work.append(self.gpa, field.ty);
                    }
                    try work.append(self.gpa, record.ext);
                },
                .tag_union => |union_ty| {
                    var tags = union_ty.tags.iterator();
                    while (tags.next()) |variant| try work.appendSlice(self.gpa, variant.args);

                    try work.append(self.gpa, union_ty.ext);
                },
                .empty_record, .empty_tag_union, .pending, .err => {},
            }
        }
    }

    fn mentionsIn(self: *Reifier, id: CheckedTypeId, vars: *const RowVars, seen: *RowVars) Allocator.Error!bool {
        return typeMentionsIn(self.gpa, self.types, id, vars, seen);
    }

    /// Whether the shape of `id` holds a variable of `vars`: as `mentionsIn`,
    /// but a variable's `where` constraints are not read, because a type
    /// whose shape is fixed is fixed whatever its constraints name.
    fn mentionsShapeOf(self: *Reifier, id: CheckedTypeId, vars: *const MentionVars, seen: *MentionVars) Allocator.Error!bool {
        if ((try seen.getOrPut(self.gpa, id)).found_existing) return false;
        switch (self.types.payload(id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .flex, .rigid => return vars.contains(id),
            .alias => |alias| return self.mentionsShapeOf(alias.backing, vars, seen),
            .function => |fn_ty| {
                for (fn_ty.args) |arg| if (try self.mentionsShapeOf(arg, vars, seen)) return true;
                return self.mentionsShapeOf(fn_ty.ret, vars, seen);
            },
            .nominal => |nominal| {
                for (nominal.args) |arg| if (try self.mentionsShapeOf(arg, vars, seen)) return true;
                return false;
            },
            .tuple => |parts| {
                for (parts) |part| if (try self.mentionsShapeOf(part, vars, seen)) return true;
                return false;
            },
            .record => |record| {
                var fields = record.fields.iterator();
                while (fields.next()) |field| if (try self.mentionsShapeOf(field.ty, vars, seen)) return true;
                return self.mentionsShapeOf(record.ext, vars, seen);
            },
            .tag_union => |union_ty| {
                var variants = union_ty.tags.iterator();
                while (variants.next()) |variant| {
                    for (variant.args) |arg| if (try self.mentionsShapeOf(arg, vars, seen)) return true;
                }
                return self.mentionsShapeOf(union_ty.ext, vars, seen);
            },
            .empty_record, .empty_tag_union, .pending, .err => return false,
        }
    }

    /// A lambda the block bound, lifted into a row of its own (N8b), or the
    /// definition a call fixed a parameter to.
    ///
    /// A lambda the block generalized is built at the type `use`, the type
    /// the lookup instantiated its scheme to, so each type it is called at
    /// keys a row of its own.
    fn liftedTarget(self: *Reifier, binding: Binding, use: CheckedTypeId, use_expr: ?ExprId, region: base.Region) Error!Callee {
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
    /// walks it, a builtin, or a function in the site's cut.
    ///
    /// Every hop is a ref the producer recorded: the reference names a
    /// binding, the binding names a template, and the template holds the body.
    ///
    /// `written_binder` is what the call site's own name binds, which names a
    /// definition of this module.
    fn resolvedTarget(self: *Reifier, resolved: checked.ResolvedValueRefId, written_binder: ?BinderId, region: base.Region, use_kind: CalleeUse) Error!Callee {
        // A top-level value that computes a function is no definition. A call
        // on it is the call of the definition it is written as when that is a
        // curried call (`curriedCall`), and otherwise an `Apply` of the value
        // it is written as, which the builder resolves once the value is a
        // known closure.
        if (try self.computedFunction(resolved, region) != null) return .value;
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
        // An intrinsic has no body: it is a `Prim` at every site, whatever
        // the site's cut says, and an instance table names no definition
        // for it.
        if (try self.intrinsicCallee(use.binding)) |intrinsic| {
            return .{ .foreign = withEvidence(intrinsic.name, intrinsic.requirements()) };
        }
        const reached = try self.reachedProcedure(use.binding, written_binder, region);
        const reader = reached.reader;
        // A primitive (D1) is named: a builtin by its export name, an
        // operation of an opaque type by its qualified name. A function in
        // the site's cut is named by its qualified name (N8h), and every
        // other function, in any package, is the definition to walk (N8l).
        // A builtin is named wherever it is called, the builtin module's own
        // bodies included. A first stage walks the Roc definition of a
        // builtin that hands back a function, and names every other. An
        // instance table names no primitive and no cut.
        const primitive: ?Primitive = if (use_kind == .instance_table)
            null
        else if (reader.names.procBase(reached.template.proc_base).source_def_idx) |def|
            try reader.primitiveOf(@fromBackingInt(def), reached.template.checked_fn_root)
        else if (reader.env.module_role == .builtin) .builtin else null;
        // A primitive's `where` requirements are its template's, which the
        // call answers (D7).
        const requirements = PrimEvidence.of(reader, reached.template);
        if (primitive) |found| switch (found) {
            .builtin => if (!self.walk.open_builtins) {
                const export_name = providedName(reader.names, reached.template) orelse
                    return self.rejectError(.unsupported_expression, region, "a call to a function the compiler provides");
                return .{ .provided = .{ .name = export_name.text, .role = roleOf(use.iterator_procedure), .evidence = requirements } };
            },
            .operation => |name| return .{ .foreign = withEvidence(name, requirements) },
        } else if (use_kind == .described) {
            if (self.inCut(reader, reached.body)) |name| return .{ .foreign = withEvidence(name, requirements) };
        }
        // What the use copied the procedure's variables to is keyed by the
        // use, and only a use of the procedure's own scheme has it.
        const written = self.value_refs.records[@backingInt(resolved)];
        const use_expr = if (reached.forwarded or written.ref == .local_proc) null else written.expr;
        var instance = if (reached.alias) |hop|
            try self.instantiationThroughAlias(reader, reached.template, hop, written.expr)
        else
            try reader.instantiationOf(reader.templateScheme(reached.template), self, use.source_fn_ty_payload, use_expr, region, .call);
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        // The use recorded the type it instantiated the scheme at, which is
        // what Monotype specializes a direct call's target at.
        const signature: ?FramedType = if (instance == null) null else if (use.source_fn_ty_payload) |payload| self.resolvedType(payload) else null;
        return .{ .definition = .{
            .key = .{
                .artifact = reader.artifact.bytes,
                .body = reached.body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .reader = reader,
            .instantiation = instance,
            .signature = signature,
        } };
    }

    /// The procedure a binding names, with every exact alias on the way
    /// followed: the reader of the module that defines it, its body, and its
    /// template.
    const ReachedProcedure = struct {
        reader: *Reifier,
        body: ExprId,
        template: checked.CheckedProcedureTemplate,
        /// What the procedure's own name binds in `reader`'s module.
        binder: ?BinderId,
        /// Whether an exact alias was followed to get here. A use then
        /// instantiates the alias's scheme, not the procedure's.
        forwarded: bool = false,
        /// The first lookup of the chain of exact aliases followed, the one
        /// the binding the use names forwards through, when `forwarded`.
        alias: ?AliasHop = null,
    };

    fn reachedProcedure(
        self: *Reifier,
        binding: checked.ProcedureBindingRef,
        written_binder: ?BinderId,
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
        written_binder: ?BinderId,
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
                const template = self.callable_eval_templates.templates[@backingInt(id)];
                const lookup = template.forwarded_lookup orelse
                    return self.rejectError(.unsupported_expression, region, "a top-level constant that computes a function, named as the function to describe");
                var reached = try self.forwardedProcedure(lookup, region);
                reached.alias = self.bindingHop(template, lookup);
                return reached;
            },
            .checked_error => return self.rejectError(.unresolved_reference, region, "this call"),
        };
        const templates = self.procedure_templates.templates.items;
        const raw = @backingInt(template_ref.template);
        if (raw >= templates.len) return self.rejectError(.unresolved_reference, region, "this call");
        const template = templates[raw];
        const body = switch (template.body) {
            .checked_body => |root_expr| root_expr,
            .intrinsic_wrapper, .entry_wrapper => return self.rejectError(.unresolved_reference, region, "this call"),
            // The walk never asks for an intrinsic's body (`intrinsicCallee`).
            .unimplemented => {
                std.debug.assert(!self.templateIsIntrinsic(template));
                return self.rejectError(.unresolved_reference, region, "this call");
            },
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
                .binder = binding_ref.pattern,
            };
        }
        const alias = self.walk.foreign.findExportedAlias(binding_ref.artifact, binding_ref.def) orelse
            return self.rejectError(.unsupported_expression, region, "a call to a function in a module this one does not read");
        const reader = try self.walk.reader(alias.module);
        var reached = try reader.forwardedProcedure(alias.lookup, region);
        reached.alias = reader.bindingHop(reader.callable_eval_templates.templates[@backingInt(alias.template)], alias.lookup);
        return reached;
    }

    /// The procedure the lookup an exact alias forwards to names. The
    /// checker forwards an alias only to a lookup of a procedure it can call
    /// directly, and an alias of an alias only once that alias forwards, so
    /// the hops end.
    fn forwardedProcedure(self: *Reifier, lookup: ExprId, region: base.Region) Error!ReachedProcedure {
        const resolved = self.bodies.resolvedRef(lookup) orelse
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
        const data = self.bodies.exprData(lookup);
        const binder: ?BinderId = if (data == .lookup_local) data.lookup_local else null;

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
        /// Its `where` requirements and what the call recorded for them (D7).
        evidence: PrimEvidence = .{},
    };

    /// The role of the iterator procedure the checker recorded, when the walk
    /// has a rule for it.
    fn roleOf(procedure: ?checked.IteratorProcedureId) ir.IteratorRole {
        return switch (procedure orelse return .none) {
            .identity => .identity,
            .next => .next,
            .list_iter => .list_iter,
            .map => .map,
            .custom, .single, .list_iter_rev, .str_iter_utf8, .keep_if, .drop_if, .take_first, .drop_first, .concat, .append, .with_index, .step_by, .from_iter, .range_iter, .numeric_range_iter, .numeric_to, .numeric_until, .from_step, .range_done => .none,
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
    /// or a method in the site's cut, or the derivation the checker chose.
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
            .checked_error => return self.rejectError(.unresolved_reference, region, "this call"),
            // A dispatcher no edge pins reaches the method of its default
            // owner when the walk seals it (`defaultOwnerMethod`).
            .@"unreachable" => if (self.defaultOwnerMethod(plan.resolution, plan.dispatcher_ty, plan.method) == null) {
                return self.rejectError(.unresolved_reference, region, "this call");
            },
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
                break :blk try self.numeralArgument(numeral_operand, try self.conversionParam(plan, region));
            },
            .generated_quote => |raw_node| blk: {
                generated = .quote;
                var text = std.ArrayList(u8).empty;
                defer text.deinit(self.gpa);
                try self.bodies.appendText(self.gpa, self.bodies.quoteText(raw_node), &text);
                break :blk try self.bld().litStr(text.items);
            },
            .generated_interpolation_segments => invariant("an interpolation's plan is walked by its literal"),
            .literal_pattern_value => |pattern| try self.literalPatternValue(pattern, region),
            .literal_pattern_conversion => |pattern| try self.patternLiteralConversion(pattern, region),
            // Only the encoder plan of a bound capture read passes the
            // site's default, and the walk never dispatches that plan: a
            // slot records the read as its encoder (`SlotSource.encoder`).
            .bound_capture_default => invariant("the walk dispatches a bound capture encoder plan"),
        };

        return self.dispatchWithArgs(DispatchSpec.ofPlan(plan), args, generated, result_ty, region);
    }

    /// The `Num.Numeral` the compiler hands to a `from_numeral` conversion,
    /// of the type `ty` the conversion's parameter has: one `Lit` of the sign
    /// and the digits the literal spells, the value Monotype builds
    /// (`lowerNumeralValue`).
    fn numeralArgument(self: *Reifier, literal: ModuleEnv.NumeralLiteral, ty: TyId) Error!Ref {
        if (!literal.isMaterialized()) invariant("a from_numeral argument literal was not materialized");
        return self.bld().litNumeral(
            ty,
            literal.isNegative(),
            self.env.numeralDigitsBefore(literal),
            self.env.numeralDigitsAfter(literal),
            literal.after_decimal_digit_count,
        );
    }

    /// The value a custom literal pattern matches, which `guardedTest` binds
    /// the pattern to.
    fn literalPatternValue(self: *Reifier, pattern: PatternId, region: base.Region) Error!Ref {
        const binding = self.lookupBinding(pattern) orelse
            invariant("a literal pattern's equality reads a pattern its test did not bind");
        return self.bindingValue(binding, self.bodies.patternType(pattern), null, region);
    }

    /// A custom literal pattern's literal converted at the pattern's type,
    /// built as the same literal written as an expression is
    /// (`numeralExpr`, the `.str` arm of `ownAs`).
    fn patternLiteralConversion(self: *Reifier, pattern: PatternId, region: base.Region) Error!Ref {
        const conversion = self.bodies.literalConversion(@backingInt(pattern));
        switch (conversion.literal) {
            .numeral => |literal| if (self.builtinNominalOf(conversion.ty)) |primitive| {
                return self.numeralLit(literal, primitive, try self.tyOf(conversion.ty, region), region);
            },
            .quote => |text| {
                const ty = try self.tyOf(conversion.ty, region);
                if (self.rt().get(ty) == .str) {
                    var bytes = std.ArrayList(u8).empty;
                    defer bytes.deinit(self.gpa);
                    try self.bodies.appendText(self.gpa, text, &bytes);
                    return self.bld().litStr(bytes.items);
                }
            },
        }
        if (conversion.conversion_root) |root| try self.walk.noteRead(self.artifact, root);
        return self.dispatchExpr(conversion.plan, conversion.ty, region);
    }

    /// The type of the one parameter of the conversion a plan calls: the
    /// `Num.Numeral` the callable the checker solved takes.
    fn conversionParam(self: *Reifier, plan: static_dispatch.StaticDispatchCallPlan, region: base.Region) Error!TyId {
        const function = self.functionOf(plan.callable_ty) orelse invariant("a from_numeral callable is not a function");
        if (function.args.len != 1) invariant("a from_numeral callable does not take one argument");
        return self.tyOf(function.args[0], region);
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

    /// `generated` says an operand is one the compiler wrote: the
    /// `Num.Numeral` literal of a number (`numeralArgument`), or the text of
    /// a quote. A `Prim` takes it as its signature says. A row's parameter
    /// has the type the method declares, so the numeral is built at that
    /// type, and the row's `Try` is read as the checker reads
    /// a conversion: the `Ok` payload is the literal's value, and an `Err`
    /// is a literal the conversion rejected.
    fn dispatchWithArgs(self: *Reifier, spec: DispatchSpec, args: []const Ref, generated: Generated, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const b = self.bld();
        const inline_call = generated == .none and try self.walksInline(result_ty, region);
        self.walk.open_builtins = inline_call;
        const found = self.dispatchTarget(spec, region, .described) catch |err| {
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
            .foreign => |name| return self.foreignPrim(name, args, try self.tyOf(result_ty, region), region),
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

    /// The slot a dispatch that forwards to an evidence param shares its
    /// target with, where the supplied entry relates the slot's target to its
    /// own callable (`sharedTarget`), or null for any other dispatch.
    fn sharedDispatch(self: *Reifier, resolution: static_dispatch.CheckedCallResolution) ?SuppliedEntry {
        const forwarded = switch (resolution) {
            .evidence_dependent => |forwarded| forwarded,
            .direct_closed, .direct_parametric, .direct_pending, .structural, .checked_error, .@"unreachable" => return null,
        };
        if (forwarded.index.depth != 0 or forwarded.index.index >= self.evidence.entries.len) return null;
        const entry = self.evidence.entries[forwarded.index.index];
        const constraint = switch (entry.evidence.resolution) {
            .constraint => |constraint| constraint,
            .direct, .structural, .from_callable, .from_scheme, .checked_error, .unreachable_value => return null,
        };
        return sharedTarget(constraint, entry.scope);
    }

    /// What a dispatch's callee is from the walk's side.
    const DispatchCallee = union(enum) {
        /// A body the walk builds a row for.
        definition: CalleeTarget,
        /// A builtin, by its export name.
        provided: Provided,
        /// An operation of an opaque type (D1), or a method in the site's
        /// cut (N8h).
        foreign: ForeignName,
        /// Nothing the walk reaches.
        none,
    };

    fn dispatchTarget(self: *Reifier, spec: DispatchSpec, region: base.Region, use_kind: CalleeUse) Error!DispatchCallee {
        const method = self.names.methodNameText(spec.method);
        if (self.dispatchEdge(spec.resolution)) |edge| {
            return self.methodTargetCallee(edge.reader, edge.node.target, .{ .edge = edge }, region, use_kind);
        }
        // A requirement the alias's own annotation forwards relates the
        // slot's target to this use's callable (`independent_callable`). The
        // target is the slot's, and the dispatcher this call fixes names the
        // instance, as Monotype rebuilds the target without the slot's
        // instantiation.
        if (self.sharedDispatch(spec.resolution)) |slot| switch (slot.evidence.resolution) {
            .direct => |node_id| {
                const node = slot.reader.plans.evidenceNode(node_id);
                return slot.reader.methodTargetCallee(slot.reader, node.target, .{ .receiver = self.resolvedType(spec.dispatcher_ty) }, region, use_kind);
            },
            .structural, .unreachable_value => return .none,
            .constraint, .from_callable, .from_scheme, .checked_error => invariant("a shared slot is a target, a derivation or unreachable"),
        };
        // A body the compiler's own derivation reached is fixed by its
        // receiver, and no call supplied evidence for what it forwards. The
        // receiver fixed the dispatcher too, so the target is the method its
        // nominal declares, read from the registry the derivation read.
        if (spec.resolution == .evidence_dependent and self.evidence.reader == null) {
            const fixed = self.fixedType(spec.dispatcher_ty) orelse return .none;
            const target = receiverMethod(fixed, method) orelse return .none;
            return fixed.reader.methodTargetCallee(fixed.reader, target, .{ .receiver = fixed }, region, use_kind);
        }
        if (self.defaultOwnerMethod(spec.resolution, spec.dispatcher_ty, spec.method)) |target| {
            return self.methodTargetCallee(self, target, .{ .receiver = self.resolvedType(spec.dispatcher_ty) }, region, use_kind);
        }
        return .none;
    }

    /// The method a dispatch reaches whose dispatcher no edge pins and the
    /// walk seals to its numeric default (`defaultedVariable`): the default
    /// owner's registered method, or null for any other dispatch.
    ///
    /// Checking unifies a defaulting dispatcher with its default owner only
    /// where a value of the program reaches it, so the dispatch of a
    /// parameter of a lambda at a `Code` position, which nothing calls, is
    /// left `unreachable`, with no target selected. A description is the
    /// specialization that reaches it, at the type the walk seals the
    /// dispatcher to, so the method is the one that type's owner registers,
    /// read from the registries as a receiver's method is
    /// (`receiverMethod`). `relateSelectedTargets` relates it to the
    /// dispatch's callable, and marks a dispatcher whose default's method
    /// does not fit it (`x` in `|x| x * 2.U8`).
    fn defaultOwnerMethod(self: *Reifier, resolution: static_dispatch.CheckedCallResolution, dispatcher_ty: CheckedTypeId, method: canonical.MethodNameId) ?static_dispatch.MethodTarget {
        if (resolution != .@"unreachable") return null;
        const variable = switch (self.types.payload(self.throughAliases(dispatcher_ty))) {
            .flex, .rigid => |variable| variable,
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .pending, .err, .alias, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => return null,
        };
        const sealed = defaultedVariable(variable) orelse return null;
        const owner: ForeignNominal = .{
            .module = &self.artifact.bytes,
            .source_decl = 0,
            .builtin = static_dispatch.builtinOwnerForCheckedBuiltin(defaultBuiltin(sealed)),
        };
        return self.walk.foreign.findMethod(owner, self.names.methodNameText(method));
    }

    /// The target the method registries declare for `method` on the nominal
    /// `fixed` is, the lookup a dispatch the compiler's own derivation reached
    /// makes. Null where `fixed` is no nominal or no registry in reach
    /// declares the method.
    fn receiverMethod(fixed: FramedType, method: []const u8) ?static_dispatch.MethodTarget {
        const nominal = fixed.reader.nominalOf(fixed.id) orelse return null;
        return fixed.reader.walk.foreign.findMethod(fixed.reader.foreignNominal(nominal), method);
    }

    /// How a call fixes a method's quantified variables and discharges its
    /// obligations: off the dispatch's edge, or, for a method the compiler's
    /// own derivation reached, off the receiver's type.
    const MethodFixing = union(enum) {
        edge: DispatchEdge,
        receiver: FramedType,
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
        region: base.Region,
        use_kind: CalleeUse,
    ) Error!DispatchCallee {
        const procedure = switch (target.kind) {
            .procedure => |procedure| procedure,
            // The walk does not read the value of a method bound to a
            // computed callable (`to_inspect = make()`), so a call of it has
            // no target. Its entry wrapper computes the value, and an
            // instance table describes the wrapper at the edge.
            .callable_binding => |binding| return switch (use_kind) {
                .instance_table => switch (fixing) {
                    .edge => |edge| try owner.computedMethodCallee(binding, edge, region),
                    // A derivation reaches a method by its owner type, which
                    // the type's own occurrence describes (Q17).
                    .receiver => .none,
                },
                .described => .none,
            },
            .local_proc, .structural => return .none,
        };
        // A method bound to another function by name (`method = f`) is
        // reached through that alias: the edge fixes the alias's quantified
        // variables and answers the alias's requirements, not the target's
        // (`EvidenceNested.through_alias`). The reader of the target's
        // template module holds the definition. The alias can be in a
        // different module (`method = Other.f`), and the reader of that
        // module holds the alias chain, through which the target's own
        // evidence is composed.
        const defining = if (target.alias != null)
            try owner.templateReader(procedure.template.artifact) orelse return .none
        else
            owner;
        const alias_holder = if (target.alias) |alias|
            try owner.templateReader(alias.module) orelse return .none
        else
            owner;
        // An intrinsic has no body: it is a `Prim` at every site, whatever
        // the site's cut says, and an instance table names no definition
        // for it.
        const def = try owner.methodTargetDef(procedure, target) orelse return .none;
        if (try defining.intrinsicOfTemplate(procedure.template.artifact, def)) |intrinsic| {
            const aliased = try aliasedEvidence(owner, alias_holder, target, fixing);
            return .{ .foreign = withEvidence(intrinsic.name, answeredBy(intrinsic.requirements(), owner, fixing, aliased)) };
        }
        const found = defining.methodDefinition(procedure.template, def) orelse return .none;
        const reader = switch (found) {
            .provided => |builtin| try self.walk.reader(builtin.definition.module),
            .here, .here_builtin => defining,
            .away => |definition| try self.walk.reader(definition.module),
        };
        const aliased = try aliasedEvidence(owner, alias_holder, target, fixing);
        // A primitive (D1) is named as the direct call of the same
        // definition names it: a builtin by its export name, an operation of
        // an opaque type by its qualified name. A method in the site's cut is
        // named by its qualified name (N8h); every other method, in any
        // package, is walked (N8l).
        // A primitive's `where` requirements are its template's, and the
        // edge's nested evidence answers them (D7). An edge that derives
        // that evidence from its callable records none. A method the
        // compiler's own derivation reached records none by construction,
        // and its receiver answers them (`receiverEvidence`).
        // An instance table names no primitive and no cut.
        if (use_kind == .described) {
            const requirements = answeredBy(PrimEvidence.of(reader, found.template()), owner, fixing, aliased);
            if (try reader.primitiveOf(def, found.template().checked_fn_root)) |primitive| switch (primitive) {
                .builtin => if (!self.walk.open_builtins) {
                    const name = switch (found) {
                        .provided => |builtin| builtin.name,
                        .here_builtin => |builtin| builtin.name,
                        .here, .away => invariant("a function of the builtin module is read as a builtin"),
                    };
                    return .{ .provided = .{ .name = name, .role = roleOf(procedure.runtime_target.iteratorProcedure()), .evidence = requirements } };
                },
                .operation => |name| return .{ .foreign = withEvidence(name, requirements) },
            } else if (self.inCut(reader, found.body())) |name| return .{ .foreign = withEvidence(name, requirements) };
        }
        var instance = switch (fixing) {
            .edge => |edge| switch (edge.node.nested) {
                .resolved, .from_callable => try owner.dispatchInstantiation(reader, found.template(), edge.node, region),
                .through_alias => try owner.aliasInstantiation(reader, found.template(), edge.node, target.alias.?, alias_holder),
            },
            .receiver => |receiver| try reader.receiverInstantiation(found.template(), receiver, region),
        };
        errdefer if (instance) |*fixed| fixed.substitution.deinit(self.gpa);
        // The edge recorded the callable it related the target to, which is
        // what Monotype specializes the target at. A derivation records none,
        // and a definition with no variables has the one type.
        const signature: ?FramedType = if (instance == null) null else switch (fixing) {
            .edge => |edge| switch (edge.node.instantiation) {
                .callable, .alias, .derived_from_callable => |callable| owner.resolvedType(callable),
                .monomorphic => null,
            },
            .receiver => null,
        };
        return .{
            .definition = .{
                .key = .{
                    .artifact = reader.artifact.bytes,
                    .body = found.body(),
                    .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
                },
                .reader = reader,
                .instantiation = instance,
                .signature = signature,
                .evidence = switch (fixing) {
                    .edge => |edge| switch (edge.node.nested) {
                        .resolved => try owner.supply(owner.plans.nestedEvidence(edge.node), edge.scope),
                        // The edge derives the target's evidence from its
                        // callable rather than recording it, so the walk of the
                        // body has no answer to read.
                        .from_callable => .{},
                        .through_alias => if (aliased) |recorded| try recorded.reader.supply(recorded.entries, recorded.scope) else .{},
                    },
                    // A derivation records no evidence, because the checker
                    // planned no call.
                    .receiver => .{},
                },
            },
        };
    }

    /// The entry wrapper of the computed callable `binding` names, which
    /// computes the value of a method bound to it (`encoder_for = make({})`)
    /// and holds the inventory of the binding's body. Null where the walk
    /// cannot read the binding's module.
    fn computedMethod(self: *Reifier, binding: static_dispatch.CallableBindingTarget) Allocator.Error!?UsedTemplate {
        const reader = try self.templateReader(binding.module) orelse return null;
        const eval_template = reader.callable_eval_templates.templates[@backingInt(binding.template)];
        const wrapper = reader.entry_wrappers.lookupByRoot(eval_template.root) orelse
            invariant("a method bound to a computed callable has no entry wrapper");
        return .{ .reader = reader, .template = wrapper.template.template, .body = eval_template.body };
    }

    /// The entry wrapper of a method bound to a computed callable, at the
    /// instance an edge selects (design.md "Code Instance Tables"). The
    /// wrapper's scheme is over the variables its value leaves free, so the
    /// function type the wrapper returns is matched with the callable the
    /// edge related the method to, as a descriptor method's template is
    /// matched with its owner type (`instantiationAtOwner`). The wrapper
    /// takes no `where` evidence.
    fn computedMethodCallee(self: *Reifier, binding: static_dispatch.CallableBindingTarget, edge: DispatchEdge, region: base.Region) Error!DispatchCallee {
        const found = try self.computedMethod(binding) orelse return .none;
        const reader = found.reader;
        const template = reader.procedure_templates.templates.items[@backingInt(found.template)];
        const method_fn = (reader.functionOf(template.checked_fn_root) orelse invariant("an entry wrapper's type is a function")).ret;
        const instance = switch (edge.node.instantiation) {
            .callable, .alias, .derived_from_callable => |callable| try reader.instantiationAtOwner(.{ .vars = reader.schemeVars(template), .root = method_fn }, method_fn, self.resolvedType(callable), region),
            // A binding that leaves no variable free has one type.
            .monomorphic => blk: {
                std.debug.assert(reader.schemeVars(template).len == 0); // checking relates a generic target to the callable at its edge
                break :blk null;
            },
        };
        return .{ .definition = .{
            .key = .{
                .artifact = reader.artifact.bytes,
                .body = found.body,
                .instantiation = if (instance) |fixed| fixed.key else @as([32]u8, @splat(0)),
            },
            .reader = reader,
            .instantiation = instance,
        } };
    }

    /// What a method bound to another function by name (`method = f`) answers
    /// its target's requirements with, composed through the alias, or null
    /// for an edge that is no such method.
    fn aliasedEvidence(owner: *Reifier, alias_holder: *Reifier, target: static_dispatch.MethodTarget, fixing: MethodFixing) Error!?Recorded {
        const edge = switch (fixing) {
            .edge => |edge| edge,
            .receiver => return null,
        };
        if (edge.node.nested != .through_alias) return null;
        const held = try owner.supply(owner.plans.aliasScopeEvidence(edge.node), edge.scope);
        return try alias_holder.evidenceThroughAlias(target.alias.?, held);
    }

    /// A method target's `where` requirements `requirements`, with what its
    /// edge recorded for them, or with the receiver that answers them where
    /// the compiler's own derivation reached the target.
    fn answeredBy(requirements: PrimEvidence, owner: *Reifier, fixing: MethodFixing, aliased: ?Recorded) PrimEvidence {
        var answered = requirements;
        switch (fixing) {
            .edge => |edge| answered.recorded = switch (edge.node.nested) {
                .resolved => .{ .reader = owner, .entries = owner.plans.nestedEvidence(edge.node), .scope = edge.scope },
                .from_callable => null,
                .through_alias => aliased,
            },
            // The receiver answers what a derivation's call records nothing for.
            .receiver => |receiver| answered.receiver = receiver,
        }
        return answered;
    }

    /// Where a method's body lives: this module's tables, another module's
    /// export rows, or the builtin module, whose function carries its name.
    const MethodDefinition = union(enum) {
        here: struct { template: checked.CheckedProcedureTemplate, body: ExprId },
        /// A builtin of the module being read: the name it answers to, and
        /// its definition.
        here_builtin: struct { name: []const u8, template: checked.CheckedProcedureTemplate, body: ExprId },
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

        fn body(self: MethodDefinition) ExprId {
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
            const body = switch (template.body) {
                .checked_body => |root_expr| root_expr,
                .intrinsic_wrapper, .entry_wrapper => return null,
                // The walk never asks for an intrinsic's body.
                .unimplemented => {
                    std.debug.assert(!self.templateIsIntrinsic(template));
                    return null;
                },
            };
            if (self.env.module_role == .builtin) {
                return .{ .here_builtin = .{ .name = (providedName(self.names, template) orelse return null).text, .template = template, .body = body } };
            }
            return .{ .here = .{ .template = template, .body = body } };
        }
        const definition = self.walk.foreign.findExported(template_ref.artifact, def_idx) orelse return null;
        if (definition.module.env().module_role == .builtin) {
            return .{ .provided = .{
                .name = (providedName(definition.module.sources.bodies.names, definition.template) orelse return null).text,
                .definition = definition,
            } };
        }
        return .{ .away = definition };
    }

    /// The definition of a procedure method target's template, in the
    /// template's own module. `MethodTarget.def_idx` is the method's binding
    /// in the module that declares the method, so for a method bound by an
    /// alias (`method = f`, `method = Other.f`, design.md "Procedure
    /// Aliases") it is not the template's definition, and for a procedure of
    /// another module it is a definition of another module. Null where the
    /// walk cannot read the template's module, or the template has no
    /// definition of its own.
    fn methodTargetDef(self: *Reifier, procedure: static_dispatch.ProcedureMethodTarget, target: static_dispatch.MethodTarget) Allocator.Error!?CIR.Def.Idx {
        if (target.alias == null) return target.def_idx;
        const reader = try self.templateReader(procedure.template.artifact) orelse return null;
        const template = reader.procedure_templates.templates.items[@backingInt(procedure.template.template)];
        const def = reader.names.procBase(template.proc_base).source_def_idx orelse return null;
        return @fromBackingInt(def);
    }

    /// The reader of the module whose artifact is `artifact`, or null when the
    /// walk cannot read it.
    fn templateReader(self: *Reifier, artifact: canonical.ArtifactRef) Allocator.Error!?*Reifier {
        if (std.meta.eql(artifact.bytes, self.artifact.bytes)) return self;
        const module = self.walk.foreign.findModule(&artifact.bytes) orelse return null;
        return try self.walk.reader(module);
    }

    /// One lookup of the chain a method bound by name forwards through: the
    /// reader of the module that holds it, and the lookup.
    const AliasHop = struct {
        reader: *Reifier,
        lookup: ExprId,
        /// The quantified variables of the scope the alias owns, which an
        /// edge through it fixes and its lookup's recorded substitution is
        /// written in.
        scope_vars: []const CheckedTypeId,
    };

    /// The hop of a top-level alias binding's template, which `self` holds.
    fn bindingHop(self: *Reifier, template: checked.CallableEvalTemplate, lookup: ExprId) AliasHop {
        const wrapper = self.entry_wrappers.lookupByRoot(template.root) orelse
            invariant("a method alias binding has an entry wrapper");
        std.debug.assert(std.meta.eql(wrapper.template.artifact.bytes, self.artifact.bytes));
        const scope_template = self.procedure_templates.templates.items[@backingInt(wrapper.template.template)];
        return .{ .reader = self, .lookup = lookup, .scope_vars = self.schemeVars(scope_template) };
    }

    /// The hop of a block-local alias, which `self` holds.
    fn localHop(self: *Reifier, lookup: ExprId, dispatch_scope: ?checked.DispatchScopeId) AliasHop {
        const scope_id = dispatch_scope orelse return .{ .reader = self, .lookup = lookup, .scope_vars = &.{} };
        const scope = &self.procedure_templates.dispatch_scopes[@backingInt(scope_id)];
        return .{ .reader = self, .lookup = lookup, .scope_vars = self.procedure_templates.scopeSchemeVars(scope) };
    }

    /// The first lookup of a method alias, which `self` declares.
    fn firstAliasHop(self: *Reifier, alias: static_dispatch.MethodAlias) AliasHop {
        std.debug.assert(alias.module.eql(.{ .bytes = self.artifact.bytes }));
        switch (alias.binding) {
            .top_level => |pattern| {
                for (self.callable_eval_templates.templates) |template| {
                    if (template.pattern != pattern) continue;
                    return self.bindingHop(template, template.forwarded_lookup orelse invariant("a method alias binding is an exact procedure alias"));
                }
                invariant("a method alias binding has a callable-eval template");
            },
            .local => |local| return self.localHop(local.lookup, local.dispatch_scope),
        }
    }

    /// The lookup the alias lookup `hop` forwards to when that is itself an
    /// exact alias, or null when it names the procedure the chain ends at.
    fn nextAliasHop(hop: AliasHop) Allocator.Error!?AliasHop {
        const reader = hop.reader;
        const resolved = reader.bodies.resolvedRef(hop.lookup) orelse
            invariant("an alias forwards to a lookup with no resolved reference");
        const use = switch (reader.value_refs.records[@backingInt(resolved)].ref) {
            .local_proc => |local| return if (local.is_alias) reader.localHop(local.expr, local.dispatch_scope) else null,
            .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| use,
            .hosted_proc, .platform_required_proc => return null,
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
            => invariant("an alias forwards to a lookup that names no procedure"),
        };
        switch (use.binding) {
            .top_level => |top_level| {
                std.debug.assert(std.meta.eql(top_level.artifact.bytes, reader.artifact.bytes));
                const id = switch (reader.procedure_bindings.get(top_level.binding).body) {
                    .callable_eval_template => |id| id,
                    .direct_template, .checked_error => return null,
                };
                const template = reader.callable_eval_templates.templates[@backingInt(id)];
                const lookup = template.forwarded_lookup orelse return null;
                return reader.bindingHop(template, lookup);
            },
            .imported => |imported| {
                const alias = reader.walk.foreign.findExportedAlias(imported.artifact, imported.def) orelse return null;
                const aliased = try reader.walk.reader(alias.module);
                return aliased.bindingHop(aliased.callable_eval_templates.templates[@backingInt(alias.template)], alias.lookup);
            },
            .hosted, .platform_required => return null,
        }
    }

    /// What the chain of lookups a method alias forwards through recorded
    /// for the evidence of the procedure it ends at, or null when the last
    /// lookup recorded none. `held` is what the edge answered for the alias's
    /// own requirements: each lookup's entries forward into it, and the next
    /// lookup's entries forward into what those supply, as Monotype's
    /// `composeThroughAlias` composes the evidence alias by alias.
    fn evidenceThroughAlias(self: *Reifier, alias: static_dispatch.MethodAlias, held: SuppliedEvidence) Allocator.Error!?Recorded {
        var hop = self.firstAliasHop(alias);
        var scope = held;
        while (true) {
            const entries = hop.reader.plans.siteEvidence(hop.lookup);
            const next = try nextAliasHop(hop) orelse {
                const last = entries orelse return null;
                return .{ .reader = hop.reader, .entries = last, .scope = scope };
            };
            scope = if (entries) |recorded| try hop.reader.supply(recorded, scope) else .{};
            hop = next;
        }
    }

    /// What the edge fixes the quantified variables of the procedure a method
    /// alias ends at to. The edge's substitution fixes the alias's own
    /// variables, and each lookup of the chain recorded what it copied the
    /// next scope's variables to, written in the variables of the scope it
    /// stands in. Reading each recorded type in a frame holding the scope's
    /// binding composes the two alias by alias, as Monotype's
    /// `composeThroughAlias` does, so a variable only a `where` obligation
    /// names is fixed by the lookup that recorded it.
    fn aliasInstantiation(
        self: *Reifier,
        reader: *Reifier,
        template: checked.CheckedProcedureTemplate,
        node: static_dispatch.EvidenceNode,
        alias: static_dispatch.MethodAlias,
        alias_holder: *Reifier,
    ) Error!?Instantiation {
        const target_vars = reader.schemeVars(template);
        if (target_vars.len == 0) return null;
        const hop = alias_holder.firstAliasHop(alias);
        const edge_fixed = self.plans.targetSubstitution(node);
        if (edge_fixed.len != hop.scope_vars.len) invariant("an edge through a method alias fixes the alias scope's variables");
        var scope: Substitution = .empty;
        defer scope.deinit(self.gpa);
        for (hop.scope_vars, edge_fixed) |scope_var, use| try scope.put(self.gpa, scope_var, self.resolvedType(use));
        return self.composedThroughHops(hop, scope, target_vars);
    }

    /// What the variables of the procedure a chain of alias lookups ends at
    /// are fixed to, given `scope`: what the first hop's own variables are
    /// fixed to. Each lookup recorded what it copied the next scope's
    /// variables to, written in the variables of the scope it stands in.
    fn composedThroughHops(
        self: *Reifier,
        first: AliasHop,
        first_scope: Substitution,
        target_vars: []const CheckedTypeId,
    ) Error!?Instantiation {
        var hop = first;
        var scope = try first_scope.clone(self.gpa);
        defer scope.deinit(self.gpa);
        while (true) {
            const frame = try self.walk.pushFrame(scope);
            const copied = hop.reader.plans.siteSubstitution(hop.lookup) orelse &.{};
            const next = try nextAliasHop(hop);
            const next_vars = if (next) |following| following.scope_vars else target_vars;
            if (copied.len != next_vars.len) invariant("an alias lookup records one type per variable of the scope it instantiates");
            var composed: Substitution = .empty;
            errdefer composed.deinit(self.gpa);
            for (next_vars, copied) |next_var, copy| {
                try composed.put(self.gpa, next_var, hop.reader.resolvedTypeIn(frame, copy));
            }
            if (next) |following| {
                scope.deinit(self.gpa);
                scope = composed;
                hop = following;
                continue;
            }
            return .{ .substitution = composed, .key = try instantiationKey(composed, target_vars) };
        }
    }

    /// What a use of a binding that is an exact alias fixes the quantified
    /// variables of the procedure the alias ends at to. The use recorded what
    /// it copied the alias's own variables to, and the lookups of the chain
    /// compose the rest, as a method alias is composed (`aliasInstantiation`).
    /// The app binding of a platform requirement at the requirement's sealed
    /// solution: a closing use with no use expression (design.md "Code
    /// Instance Tables").
    fn requirementTarget(self: *Reifier, use: *const RequirementUse, region: base.Region) Error!CalleeTarget {
        const reached = try self.reachedProcedure(.{ .top_level = use.binding }, use.binder, region);
        const reader = reached.reader;
        const fixed = use.sealed orelse invariant("a refused platform requirement reached a table");
        var instance = if (reached.alias) |hop|
            try self.requirementThroughAlias(use, reader, reached.template, hop, fixed)
        else
            try reader.instantiationOf(reader.templateScheme(reached.template), self, fixed, null, region, .call);
        errdefer if (instance) |*found| found.substitution.deinit(self.gpa);
        var target: CalleeTarget = .{
            .key = .{
                .artifact = reader.artifact.bytes,
                .body = reached.body,
                .instantiation = if (instance) |found| found.key else @as([32]u8, @splat(0)),
            },
            .reader = reader,
            .instantiation = instance,
            .signature = if (instance == null) null else self.resolvedType(fixed),
        };
        const supplied = self.plans.evidence_refs[use.evidence.start..][0..use.evidence.len];
        if (supplied.len != 0) target.evidence = try self.supply(supplied, self.evidence);
        return target;
    }

    /// What a platform requirement's sealed solution fixes the variables of
    /// the procedure an exact alias binding forwards to: the alias's own
    /// scheme (its entry wrapper's) matched against the solution, carried
    /// through the alias chain.
    fn requirementThroughAlias(
        self: *Reifier,
        use: *const RequirementUse,
        reader: *Reifier,
        template: checked.CheckedProcedureTemplate,
        hop: AliasHop,
        fixed: CheckedTypeId,
    ) Error!?Instantiation {
        const target_vars = reader.schemeVars(template);
        if (target_vars.len == 0) return null;
        const alias_root = switch (self.procedure_bindings.get(use.binding.binding).body) {
            .callable_eval_template => |id| blk: {
                const alias = self.callable_eval_templates.templates[@backingInt(id)];
                const wrapper = self.entry_wrappers.lookupByRoot(alias.root) orelse
                    invariant("a procedure alias binding has no entry wrapper");
                break :blk self.procedure_templates.templates.items[@backingInt(wrapper.template.template)].checked_fn_root;
            },
            .direct_template, .checked_error => invariant("a platform requirement reached an alias through no alias binding"),
        };
        var scope: Substitution = .empty;
        defer scope.deinit(self.gpa);
        try self.matchType(&scope, hop.scope_vars, alias_root, self.resolvedType(fixed));
        return self.composedThroughHops(hop, scope, target_vars);
    }

    fn instantiationThroughAlias(
        self: *Reifier,
        reader: *Reifier,
        template: checked.CheckedProcedureTemplate,
        hop: AliasHop,
        use_expr: ExprId,
    ) Error!?Instantiation {
        const target_vars = reader.schemeVars(template);
        if (target_vars.len == 0) return null;
        const copied = self.plans.siteSubstitution(use_expr) orelse &.{};
        if (copied.len != hop.scope_vars.len) invariant("a use of an alias records one type per variable of the alias's scope");
        var scope: Substitution = .empty;
        defer scope.deinit(self.gpa);
        for (hop.scope_vars, copied) |scope_var, use| try scope.put(self.gpa, scope_var, self.resolvedType(use));
        return self.composedThroughHops(hop, scope, target_vars);
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
            // A node that derives its target's evidence from its callable
            // (a closed recursive dispatch) records no substitution: the
            // callable and the methods its requirements select fix the
            // target's variables, as both lowerings derive them.
            if (node.nested == .from_callable) return try self.derivedNodeInstantiation(reader, template, node, region);
            return self.rejectError(.unresolved_type, region, "a call to a generic method this call does not fix");
        }
        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        for (scheme_vars, fixed) |scheme_var, use| {
            try substitution.put(self.gpa, scheme_var, self.resolvedType(use));
        }
        return .{ .substitution = substitution, .key = try instantiationKey(substitution, scheme_vars) };
    }

    /// What the receiver fixes a generic method's quantified variables to, or
    /// null when the method has none: the method's first parameter matched
    /// against the receiver's type, with every variable but a row bound or a
    /// report.
    fn receiverInstantiation(
        self: *Reifier,
        template: checked.CheckedProcedureTemplate,
        receiver: FramedType,
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
        // A row variable is left unbound, as `instantiationOf` leaves it: no
        // description names one.
        var rows = try self.rowVars(template.checked_fn_root);
        defer rows.deinit(self.gpa);
        for (scheme_vars) |scheme_var| {
            if (!substitution.contains(scheme_var) and !rows.contains(scheme_var)) {
                return self.rejectError(.unresolved_type, region, "a generic method this receiver does not fix");
            }
        }
        return .{ .substitution = substitution, .key = try instantiationKey(substitution, scheme_vars) };
    }

    /// What a node that derives its target's evidence from its callable
    /// (`EvidenceNested.from_callable`) fixes the target's variables to: the
    /// target's type matched with the callable the node records, and each
    /// variable only a `where` requirement reaches fixed by the method that
    /// requirement selects (`relateDerivedEvidence`).
    fn derivedNodeInstantiation(
        self: *Reifier,
        reader: *Reifier,
        template: checked.CheckedProcedureTemplate,
        node: static_dispatch.EvidenceNode,
        region: base.Region,
    ) Error!?Instantiation {
        const callable = switch (node.instantiation) {
            .callable, .alias, .derived_from_callable => |callable| callable,
            .monomorphic => invariant("a generic target's node records the callable it relates the target to"),
        };
        const scheme = reader.templateScheme(template);
        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        try reader.matchType(&substitution, scheme.vars, scheme.root, self.resolvedType(callable));
        var deriving: std.ArrayList(DerivingKey) = .empty;
        defer deriving.deinit(self.gpa);
        try reader.relateDerivedEvidence(template, &substitution, &deriving);
        return try reader.closedInstantiation(scheme, &substitution, region, Unfixed.call);
    }

    /// One template instance whose evidence `relateDerivedEvidence` is
    /// deriving: its module, its template and the key of what its receiver
    /// fixed.
    const DerivingKey = struct { artifact: [32]u8, template: u32, instantiation: [32]u8 };

    /// Bind the variables of `template` that only its `where` requirements
    /// reach, where its evidence is derived from types: a node that derives
    /// it from its callable, or a method a type selected.
    /// Each requirement whose dispatcher `substitution` fixes selects the
    /// method its owner declares, as both lowerings select it, and the
    /// requirement's callable (`EvidenceParamRecord.callable_ty`) is matched
    /// with that method's type at the receiver. A dispatcher that another
    /// requirement's result fixes is read after that requirement, so the
    /// loop runs until no requirement binds more. A requirement whose
    /// dispatcher stays open binds nothing, and the caller reports the
    /// variable it leaves open.
    fn relateDerivedEvidence(
        self: *Reifier,
        template: checked.CheckedProcedureTemplate,
        substitution: *Substitution,
        deriving: *std.ArrayList(DerivingKey),
    ) Allocator.Error!void {
        const params = self.procedure_templates.evidenceParams(&template);
        if (params.len == 0) return;
        const scheme_vars = self.schemeVars(template);
        const related = try self.gpa.alloc(bool, params.len);
        defer self.gpa.free(related);
        @memset(related, false);
        var changed = true;
        while (changed) {
            changed = false;
            const frame = try self.walk.pushFrame(substitution.*);
            for (params, related) |param, *done| {
                if (done.*) continue;
                const dispatcher = settledType(self.resolvedTypeIn(frame, param.dispatcher_ty));
                const selected = receiverMethod(dispatcher, self.names.methodNameText(param.method)) orelse continue;
                const method_fn = try dispatcher.reader.selectedMethodType(selected, dispatcher, deriving) orelse continue;
                try self.matchType(substitution, scheme_vars, param.callable_ty, method_fn);
                done.* = true;
                changed = true;
            }
        }
    }

    /// The type of the method `target` that the receiver `receiver`
    /// selected, with every variable it names fixed, or null where the
    /// method is no procedure or leaves a variable of its type open. Its own
    /// derived evidence is related first, except where that instance is
    /// already being derived (a recursive method), whose type the receiver
    /// alone then fixes.
    fn selectedMethodType(self: *Reifier, target: static_dispatch.MethodTarget, receiver: FramedType, deriving: *std.ArrayList(DerivingKey)) Allocator.Error!?FramedType {
        const procedure = switch (target.kind) {
            .procedure => |procedure| procedure,
            .callable_binding, .local_proc, .structural => return null,
        };
        const reader = try self.templateReader(procedure.template.artifact) orelse return null;
        const template = reader.procedure_templates.templates.items[@backingInt(procedure.template.template)];
        const function = reader.functionOf(template.checked_fn_root) orelse return null;
        if (function.args.len == 0) return null;
        const scheme_vars = reader.schemeVars(template);
        var substitution: Substitution = .empty;
        defer substitution.deinit(self.gpa);
        try reader.matchType(&substitution, scheme_vars, function.args[0], receiver);
        const key: DerivingKey = .{
            .artifact = procedure.template.artifact.bytes,
            .template = @backingInt(procedure.template.template),
            .instantiation = try instantiationKey(substitution, scheme_vars),
        };
        const in_progress = for (deriving.items) |item| {
            if (std.meta.eql(item, key)) break true;
        } else false;
        if (!in_progress) {
            try deriving.append(self.gpa, key);
            defer _ = deriving.pop();
            try reader.relateDerivedEvidence(template, &substitution, deriving);
        }
        var rows = try reader.rowVars(template.checked_fn_root);
        defer rows.deinit(self.gpa);
        var open: MentionVars = .empty;
        defer open.deinit(self.gpa);
        for (scheme_vars) |scheme_var| {
            if (!substitution.contains(scheme_var) and !rows.contains(scheme_var)) try open.put(self.gpa, scheme_var, {});
        }
        if (open.count() != 0) {
            var seen: MentionVars = .empty;
            defer seen.deinit(self.gpa);
            if (try reader.mentionsShapeOf(template.checked_fn_root, &open, &seen)) return null;
        }
        return .{ .reader = reader, .id = template.checked_fn_root, .frame = try self.walk.pushFrame(substitution) };
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
        switch (derivation) {
            // A custom literal pattern's equality compares operands that are
            // no expressions (`guardedTest`), so it reads them one by one.
            .equality => {
                const operands = plan.argsSlice(self.plans);
                if (operands.len != 2) return self.rejectError(.unsupported_expression, region, "a derived equality of this arity");
                const lhs = try self.equalityOperand(operands[0], region);
                const rhs = try self.equalityOperand(operands[1], region);
                return self.eqOver(lhs.ref, rhs.ref, lhs.ty, region);
            },
            .hash => {
                const ids = try self.dispatchExprs(plan, region);
                defer self.gpa.free(ids);
                if (ids.len != 2) return self.rejectError(.unsupported_expression, region, "a derived hash of this arity");
                return self.hashExpr(ids[0], ids[1], result_ty, region);
            },
            .parser, .encoder, .map, .map_effectful => {
                const ids = try self.dispatchExprs(plan, region);
                defer self.gpa.free(ids);
                const args = try self.exprRefs(ids);

                defer self.gpa.free(args);
                return self.derivedOf(self.names.methodNameText(plan.method), plan.dispatcher_ty, args, result_ty, region);
            },
        }
    }

    /// One operand of a derived equality, and the type it is compared at.
    fn equalityOperand(self: *Reifier, operand: static_dispatch.StaticDispatchOperand, region: base.Region) Error!struct { ref: Ref, ty: CheckedTypeId } {
        return switch (operand) {
            .checked_expr => |child| .{ .ref = try self.exprRef(child), .ty = self.bodies.valueType(child) },
            .literal_pattern_value => |pattern| .{ .ref = try self.literalPatternValue(pattern, region), .ty = self.bodies.patternType(pattern) },
            .literal_pattern_conversion => |pattern| .{
                .ref = try self.patternLiteralConversion(pattern, region),
                .ty = self.bodies.literalConversion(@backingInt(pattern)).ty,
            },
            .generated_numeral, .generated_quote, .generated_interpolation_segments => self.rejectError(.unsupported_expression, region, "a compiler-generated argument"),
            .bound_capture_default => invariant("an equality's dispatch plan passes no bound capture operand"),
        };
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
            .constraint => |constraint| switch ((sharedTarget(constraint, self.evidence.entries[chain.index].scope) orelse return null).evidence.resolution) {
                .structural => |structural| structural.derivation,
                .direct, .constraint, .from_callable, .from_scheme, .checked_error, .unreachable_value => null,
            },
            .direct,
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| self.eqOver(lhs, rhs, alias.backing, region),
            .nominal => |nominal| self.nominalEq(lhs, rhs, nominal, resolved.id, region),
            .record => |record| blk: {
                var fields = std.ArrayList(FieldRef).empty;
                defer fields.deinit(self.gpa);
                var bound = std.ArrayList(BoundNominal).empty;
                defer releaseBoundNominals(self.gpa, &bound);
                try self.collectRecordFields(&fields, &bound, record.fields, record.ext, region);
                sortFieldsByLabel(fields.items);
                const l = try self.readable(lhs);
                const r = try self.readable(rhs);
                var parts = std.ArrayList(EqPart).empty;
                defer parts.deinit(self.gpa);
                for (fields.items) |field| {
                    const name = field.reader.names.recordFieldLabelText(field.field.name);
                    const ty: FramedType = .{ .reader = field.reader, .id = field.field.ty, .frame = field.frame };
                    // An optional field is read as its `OptField`, the `Try`
                    // that says whether the record holds it.
                    try parts.append(self.gpa, if (field.reader.fieldKindIn(field.frame, field.field.kind) == .optional) .{
                        .lhs = try self.optionalFieldRead(l, try self.fieldIndex(l, name, region)),
                        .rhs = try self.optionalFieldRead(r, try self.fieldIndex(r, name, region)),
                        .ty = ty,
                        .optional = true,
                    } else .{
                        .lhs = try b.field(l, try self.fieldIndex(l, name, region)),
                        .rhs = try b.field(r, try self.fieldIndex(r, name, region)),
                        .ty = ty,
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
                    .ty = .{ .reader = self, .id = element, .frame = self.frame },
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

    /// Two components a derived `==` compares, and their checked type. The
    /// components of an `optional` part are the `OptField` reads of an
    /// optional record field, and `ty` is the field's value type.
    const EqPart = struct { lhs: Ref, rhs: Ref, ty: FramedType, optional: bool = false };

    /// The comparison of one part of a derived `==`.
    fn partEq(part: EqPart, region: base.Region) Error!Ref {
        if (part.optional) return part.ty.reader.optionalFieldEq(part.lhs, part.rhs, part.ty.id, region);
        return part.ty.reader.eqOver(part.lhs, part.rhs, part.ty.id, region);
    }

    /// `OptField(record, index)`: the optional field `index` of `record`, as
    /// the `Try(value, [MissingField])` a `.?` read of it gives.
    fn optionalFieldRead(self: *Reifier, record: Ref, index: u32) Error!Ref {
        const types = self.rt();
        const value_ty = types.tySlice(types.memberSlice(types.get(self.irs().refTy(self.bld().row, record)).record)[index].tys)[0];
        return self.bld().optField(record, index, try self.missingFieldTry(value_ty));
    }

    /// A derived `==` over one optional record field, from the `OptField`
    /// read of each operand. The compiler stores the field as the tagged
    /// slot `[#Missing, #Present(value)]` and derives `is_eq` over that slot
    /// as over every tag union (`EqDeriver`, `src/postcheck/monotype/lower.zig`):
    /// the fields are equal where both records hold them with equal values,
    /// and where neither record holds them. So this is `tagUnionEq` over the
    /// `Try`: a switch on the left read, and in each arm a switch on the
    /// right read. Two `Ok` arms compare the values at `value_ty`, two `Err`
    /// arms are `True`, as two `#Missing` tags with no payload are, and the
    /// other arms are `False`.
    fn optionalFieldEq(self: *Reifier, lhs: Ref, rhs: Ref, value_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const b = self.bld();
        const l = try self.readable(lhs);
        const r = try self.readable(rhs);
        const ok = try self.rt().name("Ok");
        const bool_ty = try self.rt().boolTy();
        const l_names = try self.memberNames(self.irs().refTy(b.row, l), region);
        defer self.gpa.free(l_names);
        const r_names = try self.memberNames(self.irs().refTy(b.row, r), region);
        defer self.gpa.free(r_names);
        const left_arms = try self.gpa.alloc(RegionId, l_names.len);
        defer self.gpa.free(left_arms);
        const right_arms = try self.gpa.alloc(RegionId, r_names.len);
        defer self.gpa.free(right_arms);
        for (left_arms, l_names) |*left_arm, l_name| {
            left_arm.* = try b.openTagArm(l, l_name);
            for (right_arms, r_names) |*right_arm, r_name| {
                right_arm.* = try b.openTagArm(r, r_name);
                const same = if (l_name != r_name)
                    try b.litBool(false)
                else if (l_name == ok)
                    try self.eqOver(try b.payload(l, ok, 0), try b.payload(r, ok, 0), value_ty, region)
                else
                    try b.litBool(true);
                try b.close(.{ .value = &.{same} });
            }
            try b.close(.{ .value = &.{try b.switchOn(r, right_arms, &.{}, &.{bool_ty}, &.{})} });
        }
        return b.switchOn(l, left_arms, &.{}, &.{bool_ty}, &.{});
    }

    /// `And` over the comparisons of `parts`, each after the first built in
    /// an operand region, so it runs only where the ones before it held.
    fn conjunction(self: *Reifier, parts: []const EqPart, region: base.Region) Error!Ref {
        const b = self.bld();
        if (parts.len == 0) return b.litBool(true);
        const first = try partEq(parts[0], region);
        if (parts.len == 1) return first;
        const operands = try self.gpa.alloc(RegionId, parts.len - 1);
        defer self.gpa.free(operands);
        var earlier = std.ArrayList(Ref).empty;
        defer earlier.deinit(self.gpa);
        try earlier.append(self.gpa, first);
        for (parts[1..], operands) |part, *operand| {
            operand.* = try b.openOperand(earlier.items, .and_);
            const compare = partEq(part, region) catch |err| switch (err) {
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
        var variants = std.ArrayList(VariantRef).empty;
        defer variants.deinit(self.gpa);
        try self.collectVariants(&variants, tag_union.tags, tag_union.ext, region);
        if (variants.items.len == 0) return self.derivedEq(lhs, rhs, subject_id, region);
        // Each variant's name as the type table interns it, so a tag of an
        // operand finds its variant by name.
        const variant_names = try self.gpa.alloc(NameId, variants.items.len);
        defer self.gpa.free(variant_names);
        for (variants.items, variant_names) |variant, *name| name.* = try self.rt().name(variant.reader.names.tagLabelText(variant.tag.name));
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
        checked: []const VariantRef,
        names: []const NameId,
    };

    /// Whether the payloads of one variant agree, under the arms that found
    /// both operands to be it.
    fn variantEq(self: *Reifier, l: Ref, r: Ref, name: NameId, variant: VariantRef, region: base.Region) Error!Ref {
        const b = self.bld();
        const args = variant.tag.args;
        const parts = try self.gpa.alloc(EqPart, args.len);
        defer self.gpa.free(parts);
        for (args, parts, 0..) |arg, *part, k| part.* = .{
            .lhs = try b.payload(l, name, @intCast(k)),
            .rhs = try b.payload(r, name, @intCast(k)),
            .ty = .{ .reader = variant.reader, .id = arg, .frame = variant.frame },
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
        if (self.readsOpaque(nominal)) return self.derivedEq(lhs, rhs, type_id, region);
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.rejectError(.unsupported_type, region, self.names.typeNameText(nominal.name));
        var bound_args = try self.bindNominalArgs(self.frame, nominal);
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
        return .{ .written = try self.writtenMethodCall(receiver, target, args, result, region) };
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
        receiver: CheckedTypeId,
        target: static_dispatch.MethodTarget,
        args: []const Ref,
        result: TyId,
        region: base.Region,
    ) Error!Ref {
        const b = self.bld();
        const fixing: MethodFixing = .{ .receiver = self.resolvedType(receiver) };
        return switch (try self.methodTargetCallee(self, target, fixing, region, .described)) {
            .definition => |found| blk: {
                const row = try self.calledRow(found);
                break :blk try b.callRow(row, args);
            },
            .provided => |provided| try self.providedPrimAt(provided, args, result, region),
            .foreign => |name| try self.foreignPrim(name, args, result, region),
            .none => self.rejectError(.unresolved_reference, region, "a method its nominal names no target for"),
        };
    }

    /// A derived `to_hash`: each leaf fed to the hasher by the writer's
    /// `write_*` method, in the compiler's component order. Where the walk
    /// cannot expand the recipe, the node is a `Derived` the stage refuses
    /// or expands, because only the compiler's order and widths agree with
    /// the Roc side feeding the same keys.
    fn hashExpr(self: *Reifier, value_id: ExprId, hasher_id: ExprId, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const value_ty = self.bodies.valueType(value_id);
        const hasher_ty = self.bodies.valueType(hasher_id);
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
                if (self.readsOpaque(nominal)) return null;
                const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse return null;
                var bound_args = try self.bindNominalArgs(self.frame, nominal);
                defer self.releaseNominalArgs(&bound_args);
                return self.hashOver(try self.unwrapOnce(value), acc, backing, writer, hasher_ty, region);
            },
            .record => |record| {
                var fields = std.ArrayList(FieldRef).empty;
                defer fields.deinit(self.gpa);
                var bound = std.ArrayList(BoundNominal).empty;
                defer releaseBoundNominals(self.gpa, &bound);
                try self.collectRecordFields(&fields, &bound, record.fields, record.ext, region);
                sortFieldsByLabel(fields.items);
                // The compiler hashes an optional field as its tagged slot
                // `[#Missing, #Present(value)]`, and the walk leaves the hash
                // of a tag union to the stage.
                for (fields.items) |field| {
                    if (field.reader.fieldKindIn(field.frame, field.field.kind) == .optional) return null;
                }
                const subject = try self.readable(value);
                var threaded = acc;
                for (fields.items) |field| {
                    const name = field.reader.names.recordFieldLabelText(field.field.name);
                    const component = try b.field(subject, try self.fieldIndex(subject, name, region));
                    threaded = blk: {
                        const outer_frame = field.reader.frame;
                        field.reader.frame = field.frame;
                        defer field.reader.frame = outer_frame;
                        break :blk try field.reader.hashOver(component, threaded, field.field.ty, writer, hasher_ty, region) orelse return null;
                    };
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
    fn inspectExpr(self: *Reifier, operand: ExprId, result_ty: CheckedTypeId, region: base.Region) Error!Ref {
        const value_ty = self.bodies.valueType(operand);
        const value = try self.exprRef(operand);
        var subject_ty = value_ty;
        while (true) switch (self.types.payload(subject_ty)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| subject_ty = alias.backing,
            .nominal => |nominal| {
                const target = self.walk.foreign.findInspectOverride(self.foreignNominal(nominal)) orelse break;
                return self.writtenMethodCall(subject_ty, target, &.{value}, try self.tyOf(result_ty, region), region);
            },
            .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => break,
        };
        return self.derivedOf("to_inspect", value_ty, &.{value}, result_ty, region);
    }

    /// The intrinsic the checker recorded for a call's callee, when the callee
    /// is a procedure the compiler implements.
    fn calleeIntrinsic(self: *Reifier, func: ExprId) ?checked.IntrinsicId {
        const resolved = switch (self.bodies.exprData(func)) {
            .lookup_external, .lookup_required, .lookup_local => self.bodies.resolvedRef(func) orelse return null,
            .numeral, .code_site, .str_segment, .str, .bytes_literal, .list, .empty_list, .tuple, .match_, .if_, .call, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .field_access, .dispatch_call, .interpolation, .structural_eq, .structural_hash, .method_eq, .type_dispatch_call, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => return null,
        };
        return switch (self.value_refs.callableTarget(resolved).ref) {
            .top_level_proc, .imported_proc => |use| use.intrinsic,
            .local_param, .local_value, .local_mutable_version, .pattern_binder, .local_proc, .selected_hoisted_const, .top_level_const, .imported_const, .hosted_proc, .platform_required_declaration, .platform_required_checked_error, .platform_required_const, .platform_required_proc, .promoted_top_level_proc => null,
        };
    }

    /// One node for a derived codec that was constructed and then run: the
    /// constructor's arguments first, the applied ones after, as one
    /// `Derived`. Null when the callee is not a derived codec.
    fn foldedCodecExpr(self: *Reifier, func: ExprId, operands: []const ExprId, result_ty: CheckedTypeId, region: base.Region) Error!?Ref {
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
    fn codecCallee(self: *Reifier, func: ExprId) ?static_dispatch.StaticDispatchPlanId {
        const callee = self.bodies.expr(func);
        if (callee.data == .lookup_local) {
            const binding = self.lookupBinding(callee.data.lookup_local) orelse return null;
            return switch (binding.kind) {
                .function => |bound| self.derivedCodecPlan(bound),
                .value, .constant, .callee => null,
            };
        }
        return self.derivedCodecPlan(func);
    }

    /// The plan behind a derived parser or encoder construction, when the
    /// expression is one.
    fn derivedCodecPlan(self: *Reifier, expr_id: ExprId) ?static_dispatch.StaticDispatchPlanId {
        const dispatched = switch (self.bodies.exprData(expr_id)) {
            .dispatch_call, .type_dispatch_call => self.bodies.dispatchPlan(@backingInt(expr_id)),

            .numeral, .code_site, .str_segment, .str, .bytes_literal, .lookup_local, .lookup_external, .lookup_required, .list, .empty_list, .tuple, .match_, .if_, .call, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .field_access, .interpolation, .structural_eq, .structural_hash, .method_eq, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => return null,
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
    fn constructsFunction(self: *Reifier, expr_id: ExprId) bool {
        const expr_data = self.bodies.expr(expr_id);
        const calls = switch (expr_data.data) {
            .call, .dispatch_call, .type_dispatch_call => true,
            .numeral, .code_site, .str_segment, .str, .bytes_literal, .lookup_local, .lookup_external, .lookup_required, .list, .empty_list, .tuple, .match_, .if_, .record, .empty_record, .block, .tag, .nominal, .zero_argument_tag, .closure, .lambda, .binop, .unary_minus, .field_access, .interpolation, .structural_eq, .structural_hash, .method_eq, .tuple_access, .runtime_error, .crash, .dbg, .expect_err, .expect, .ellipsis, .anno_only, .break_, .return_, .for_, .hosted_lambda, .run_low_level => false,
        };
        return calls and self.functionOf(expr_data.ty) != null;
    }

    // Types //

    /// The site's type for one checked type (N1b). A builtin scalar, `Str`
    /// and `List` are the normal form's own; `Bool` is `Bool`; a nominal is
    /// `Nominal(name, backing)`, and a reference back to a nominal the walk
    /// is inside is `Recursive(name)`; a builtin the normal form has no shape
    /// for, and an opaque nominal, is `Opaque(name, args)`.
    /// `tyOf` read in `frame`: the frame a type reference names its variables
    /// in, which need not be the frame the walk is in (D2).
    fn tyOfIn(self: *Reifier, frame: FrameId, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        const outer_frame = self.frame;
        self.frame = frame;
        defer self.frame = outer_frame;
        return self.tyOf(type_id, region);
    }

    fn tyOf(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        const ty = try self.tyInNominals(type_id, region);
        // Outside every nominal the type is closed, and a recursive one gets
        // its one spelling there (roc-reify-normal-form.md 2.1). Inside one,
        // a part may still name a nominal around it, and the cache can hand
        // back a part spelled at its own root, so a part is left as built.
        if (self.walk.open_nominals.items.len != 0) return ty;
        return self.rt().canonical(ty);
    }

    /// `tyOf` while the walk may be inside a nominal: a correct spelling,
    /// not yet the canonical one. `Types.canonical` alone decides T1.
    fn tyInNominals(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        // Resolving at the leaf is enough: a composite holding a variable is
        // reached by recursion into the variable itself.
        if (self.fixedType(type_id)) |fixed| {
            self.substitution_uses += 1;
            const outer_through = self.walk.through;
            if (outer_through == null) self.walk.through = .{ .reader = self, .id = type_id, .frame = self.frame };
            defer self.walk.through = outer_through;
            return fixed.reader.tyOfIn(fixed.frame, fixed.id, region);
        }
        if (self.ty_cache.get(type_id)) |cached| return cached;
        const frame = TypeFrame{ .depth = self.walk.open_nominals.items.len, .id = type_id };
        if (self.type_in_progress.contains(frame)) {
            return self.rejectError(.unsupported_type, region, "a recursive type");
        }
        try self.type_in_progress.put(self.gpa, frame, {});
        defer _ = self.type_in_progress.remove(frame);

        const uses_before = self.substitution_uses;
        const ty = try self.buildTy(type_id, region);
        // Cache only a type that stands alone. A substitution that answered
        // inside means something else at the next instantiation, and a
        // `Recursive` inside counts as one (`nominalTy`): it means something
        // else under other enclosing nominals.
        if (self.substitution_uses == uses_before) {
            try self.ty_cache.put(self.gpa, type_id, ty);
        }
        return ty;
    }

    fn buildTy(self: *Reifier, type_id: CheckedTypeId, region: base.Region) Error!TyId {
        const types = self.rt();
        const payload = self.types.payload(type_id);
        return switch (payload) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
                if (payload == .flex and payload.variableSealsToRowDefault()) break :blk switch (checked.sealedVariable(variable)) {
                    .empty_record => types.recordTy(&.{}),
                    .empty_tag_union => types.tagUnionTy(&.{}),
                    .dec, .str => unreachable, // a variable that seals to its row default has no numeric default
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
            .nominal => |nominal| self.nominalTy(nominal, region),
            .tag_union => |tag_union| self.tagUnionTy(tag_union.tags, tag_union.ext, region),
            .empty_tag_union => types.tagUnionTy(&.{}),
        };
    }

    fn tysOf(self: *Reifier, ids: []const CheckedTypeId, region: base.Region) Error![]TyId {
        return self.tysOfIn(self.frame, ids, region);
    }

    /// `tysOf` in `frame`.
    fn tysOfIn(self: *Reifier, frame: FrameId, ids: []const CheckedTypeId, region: base.Region) Error![]TyId {
        const tys = try self.gpa.alloc(TyId, ids.len);
        errdefer self.gpa.free(tys);
        for (ids, tys) |id, *ty| ty.* = try self.tyOfIn(frame, id, region);
        return tys;
    }

    /// A tag union's variants, following its extension.
    fn tagUnionTy(self: *Reifier, tags: checked.CheckedTags, ext: CheckedTypeId, region: base.Region) Error!TyId {
        var collected = std.ArrayList(VariantRef).empty;
        defer collected.deinit(self.gpa);
        try self.collectVariants(&collected, tags, ext, region);
        const specs = try self.gpa.alloc(reify.types.TagSpec, collected.items.len);
        defer self.gpa.free(specs);
        var filled: usize = 0;
        defer for (specs[0..filled]) |spec| self.gpa.free(spec.payload);
        for (collected.items, specs) |variant, *spec| {
            spec.* = .{ .name = variant.reader.names.tagLabelText(variant.tag.name), .payload = try variant.reader.tysOfIn(variant.frame, variant.tag.args, region) };
            filled += 1;
        }
        return self.rt().tagUnionTy(specs);
    }

    /// One variant a tag union's extension chain reached, with the module
    /// and frame its payload types are read in.
    const VariantRef = struct {
        reader: *Reifier,
        frame: FrameId,
        tag: checked.CheckedTag,
    };

    /// Every variant of a tag union, following its extension.
    ///
    /// A chain ending in a variable the site fixed carries on in the site's
    /// module, as `collectRecordFields` does for a record: the definition
    /// wrote the variants it named and the site's union holds the rest. That
    /// union holds the named variants too, so a variant already collected is
    /// dropped where it comes round a second time.
    ///
    /// A variable nothing fixed ends the chain, sealed to the empty union the
    /// way Monotype seals a row (`lowerCheckedTypeVariable`): a variable the
    /// checker closed carries the default that says so, and one nothing closed
    /// stands for the variants the definition names and no others.
    fn collectVariants(
        self: *Reifier,
        collected: *std.ArrayList(VariantRef),
        tags: checked.CheckedTags,
        ext: CheckedTypeId,
        region: base.Region,
    ) Error!void {
        var reader = self;
        var frame = self.frame;
        var link_tags = tags;
        var link_ext: ?CheckedTypeId = ext;
        while (true) {
            var link = link_tags.iterator();
            while (link.next()) |tag| try self.collectVariant(collected, reader, frame, tag);
            const next = link_ext orelse break;
            switch (reader.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .empty_tag_union => break,
                .tag_union => |more| {
                    link_tags = more.tags;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_tags = .empty;
                    link_ext = alias.backing;
                },
                .flex, .rigid => {
                    const bound = reader.fixedTypeIn(frame, next) orelse break;
                    // The variants from here on are what one site fixed, so
                    // the frame that asked declines to cache this type.
                    self.substitution_uses += 1;
                    reader = bound.reader;
                    frame = bound.frame;
                    link_tags = .empty;

                    link_ext = bound.id;
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

    /// Collect one variant, unless a link nearer the front of the chain
    /// already named it.
    fn collectVariant(self: *Reifier, collected: *std.ArrayList(VariantRef), reader: *Reifier, frame: FrameId, tag: checked.CheckedTag) Allocator.Error!void {
        for (collected.items) |seen| {
            if (seen.reader.sameTagLabel(seen.tag.name, reader, tag.name)) return;
        }
        try collected.append(self.gpa, .{ .reader = reader, .frame = frame, .tag = tag });
    }

    /// Whether the walk reads `nominal` as an opaque type: a `::` nominal,
    /// unless the site reads the opaque types of packages as their backings
    /// (`Walk.opaque_backings`). A nominal of the builtin module keeps its
    /// hidden representation (`isBuiltinNominal`): also one the checker does
    /// not mark as a builtin, such as `Num.Numeral`.
    fn readsOpaque(self: *Reifier, nominal: checked.CheckedNominalType) bool {
        if (!nominal.is_opaque) return false;
        return !(self.walk.opaque_backings and !self.isBuiltinNominal(nominal));
    }

    fn nominalTy(self: *Reifier, nominal: checked.CheckedNominalType, region: base.Region) Error!TyId {
        const types = self.rt();
        // The checker reads a capture's nominal the same way
        // (`code_opacity.nominalRead`), so the slots that hold an opaque
        // type are the reads it required an encoder for.
        const owner: ?static_dispatch.BuiltinOwner = if (nominal.builtin) |builtin_nominal|
            if (builtin_nominal == .try_) null else static_dispatch.builtinOwnerForCheckedBuiltin(builtin_nominal)
        else
            null;
        if (code_opacity.nominalRead(owner, self.readsOpaque(nominal)) == .opaque_) return self.opaqueTy(nominal, region);
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
                => unreachable, // read as opaque above
            }
        }
        const backing = self.types.nominalBackingTemplateForPayload(nominal) orelse
            return self.opaqueTy(nominal, region);
        const name = self.names.typeNameText(nominal.name);

        // A `Recursive(name)` refers to the nearest enclosing nominal of
        // that name, so this use closes only where that nominal is this
        // instance. Under any other one it expands again (T1). The key reads
        // this use's arguments under the bindings around it, before this use
        // binds its own: `Tree(a)` inside `Tree(Str)` reads `a` as `Str`.
        const instance = try self.nominalInstanceKey(nominal);
        const open = &self.walk.open_nominals;
        if (nearestOpen(open.items, self, nominal.name)) |at| {
            if (open.items[at].instance.eql(instance)) {
                // What this means depends on the nominals around it, so the
                // frames that asked decline to cache it.
                self.substitution_uses += 1;
                return types.recursiveTy(name);
            }
        }
        if (expansionRepeats(open.items, self, nominal.name, instance)) {
            return self.rejectError(.unsupported_type, region, "a recursive type with no finite description");
        }
        try open.append(self.gpa, .{ .reader = self, .name = nominal.name, .instance = instance });
        defer _ = open.pop();

        // The arguments are inside the nominal, as its backing is, so an
        // argument that holds this instance refers back to it (T1). They are
        // read before this use binds its own variables, as the key is.
        const args = try self.tysOf(nominal.args, region);
        defer self.gpa.free(args);

        // The backing is the declaration's template, written in the nominal's
        // own variables, and `args` is what this use fixed them to.
        var bound_args = try self.bindNominalArgs(self.frame, nominal);
        defer self.releaseNominalArgs(&bound_args);

        const backing_ty = try self.tyOf(backing, region);
        return self.rt().nominalTy(name, try self.nominalOrigin(nominal), args, backing_ty);
    }

    /// The position of the nearest nominal that `open` holds with the name
    /// that `name` of the store of `reader` names.
    fn nearestOpen(open: []const Walk.OpenNominal, reader: *Reifier, name: canonical.TypeNameId) ?usize {
        var at = open.len;
        while (at > 0) {
            at -= 1;
            if (open[at].reader.sameTypeName(open[at].name, reader, name)) return at;
        }
        return null;
    }

    /// Whether expanding `instance` inside `open` repeats an expansion that
    /// `open` already holds: the same instance, with the same nearest nominal
    /// for each name. What an expansion builds depends only on these, so a
    /// repeat builds itself again inside itself, and the T1 tree of the type
    /// is infinite. `Tree(a) := [Leaf(a), S(Tree(Str)), U(Tree(U64))]` is one.
    ///
    /// Instances and names are finite, so a walk that expands only where
    /// this is false ends.
    fn expansionRepeats(open: []const Walk.OpenNominal, reader: *Reifier, name: canonical.TypeNameId, instance: NominalInstanceKey) bool {
        for (open, 0..) |earlier, j| {
            if (!earlier.reader.sameTypeName(earlier.name, reader, name) or !earlier.instance.eql(instance)) continue;
            // The nearest nominal of each name now is the nearest before `j`,
            // except for a name expanded at or after `j`.
            const since = open[j..];
            const same = for (since, 0..) |entry, i| {
                if (nearestOpen(since[i + 1 ..], entry.reader, entry.name) != null) continue;
                const before = nearestOpen(open[0..j], entry.reader, entry.name) orelse break false;
                if (!open[before].instance.eql(entry.instance)) break false;
            } else true;
            if (same) return true;
        }
        return false;
    }

    /// A key for one nominal at one instantiation: the declaration, and what
    /// this use fixed its variables to.
    fn nominalInstanceKey(self: *Reifier, nominal: checked.CheckedNominalType) Allocator.Error!NominalInstanceKey {
        var hasher = std.crypto.hash.Blake3.init(.{});
        hasher.update(std.mem.asBytes(&@backingInt(nominal.origin_module)));
        hasher.update(std.mem.asBytes(&@backingInt(nominal.name)));
        hasher.update(std.mem.asBytes(&nominal.source_decl));
        for (nominal.args) |arg| {
            const bound = self.resolvedType(arg);
            hasher.update(&(try bound.reader.types.rootKey(bound.id)).bytes);
        }
        var key: NominalInstanceKey = undefined;
        hasher.final(&key.bytes);
        return key;
    }

    /// The key `nominalInstanceKey` gives one nominal at one instantiation.
    const NominalInstanceKey = struct {
        bytes: [32]u8,

        /// Integer equality over the digest: a single 256-bit compare.
        fn eql(a: NominalInstanceKey, b: NominalInstanceKey) bool {
            return @as(u256, @bitCast(a.bytes)) == @as(u256, @bitCast(b.bytes));
        }
    };

    /// What one parametric nominal bound, and what stood in its place before.
    const NominalArgs = struct {
        formals: []const CheckedTypeId = &.{},
        outer: []?FramedType = &.{},
    };

    /// Bind a parametric nominal's declared variables to what this use fixed
    /// them to. Binds nothing when the nominal declares no variables, or when
    /// the declaration and the use disagree on how many there are.
    fn bindNominalArgs(self: *Reifier, frame: FrameId, nominal: checked.CheckedNominalType) Allocator.Error!NominalArgs {
        if (nominal.args.len == 0) return .{};
        const declaration = self.types.nominalDeclarationForPayload(nominal) orelse return .{};
        const formals = declaration.formalArgs(self.types);
        if (formals.len != nominal.args.len) return .{};
        // Every use is read before any formal is bound, so one formal's
        // binding cannot answer another's.
        const fixed = try self.gpa.alloc(FramedType, nominal.args.len);
        defer self.gpa.free(fixed);
        for (nominal.args, fixed) |arg, *use| use.* = self.resolvedTypeIn(frame, arg);
        const outer = try self.gpa.alloc(?FramedType, formals.len);
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
        return self.rt().opaqueTy(self.opaqueName(nominal), try self.nominalOrigin(nominal), args);
    }

    /// The name an `Opaque` gives a nominal (Q10): a builtin's is the owner
    /// its functions' `Prim`s have (`Dict`, `Box`, `Num.U8x16`), and any
    /// other nominal's is its name as the checker holds it.
    fn opaqueName(self: *Reifier, nominal: checked.CheckedNominalType) []const u8 {
        const name = self.names.typeNameText(nominal.name);
        return if (self.isBuiltinNominal(nominal)) reify.prims.ownerOfTypeName(name) else name;
    }

    /// Whether the builtin module declares a nominal (Q10): one the checker
    /// marks as a builtin (`Dict`), or any other the builtin module declares
    /// (`Hasher`), known by the role of the module its identity names.
    fn isBuiltinNominal(self: *Reifier, nominal: checked.CheckedNominalType) bool {
        return nominal.builtin != null or
            self.walk.foreign.isBuiltinModule(self.names.moduleIdentityBytes(nominal.origin_module));
    }

    /// The bits of the `Code.PrimId` of the definition the reference `arg`
    /// of a `Code.prim` call names, following exact aliases as a callee is
    /// followed: the id a `Prim` node of that definition carries. Null for a
    /// reference to no function or constant a description can name.
    fn primIdentity(self: *Reifier, arg: ExprId, source: CIR.Expr.Idx) Allocator.Error!?u128 {
        const resolved = self.lookupResolved(arg) orelse return self.derivedMethodPrim(source);
        // An intrinsic is keyed by its declaration, as any other definition
        // of a package is.
        if (try self.listedIntrinsic(resolved)) |intrinsic| {
            return reify.identity.declaredPrim(intrinsic.name.definition);
        }
        const named = try self.listedMember(resolved) orelse return null;
        if (named.reader.env.module_role != .builtin) {
            return reify.identity.declaredPrim(.{ .module = named.reader.artifact.bytes, .def = @backingInt(named.def) });
        }
        // A builtin is named by its export name, which is the name its
        // definition binds (`Builtin.Str.concat`), as `providedName` reads it.
        const env = named.reader.env;
        const ident = switch (env.store.getPattern(env.store.getDef(named.def).pattern)) {
            .assign => |assign| assign.ident,
            .var_assign,
            .as,
            .applied_tag,
            .nominal,
            .nominal_external,
            .deferred_import_ref,
            .record_destructure,
            .list,
            .tuple,
            .num_literal,
            .small_dec_literal,
            .dec_literal,
            .frac_f32_literal,
            .frac_f64_literal,
            .num_from_numeral_literal,
            .str_literal,
            .str_interpolation,
            .underscore,
            .runtime_error,
            => invariant("a builtin function binds one name"),
        };
        const export_name = reify.prims.namedOfExport(env.getIdentText(ident)) orelse
            invariant("a builtin's export name has an owner and a method");
        return reify.identity.builtinPrim(export_name.owner, export_name.method);
    }

    /// The bits of the `Code.PrimId` of the compiler-derived method (`is_eq :
    /// _`) the `Code.prim` argument `source` names, which resolves to no
    /// value. It is the id of the `Prim` the walk gives a call of the method,
    /// as `nominalEq` builds it: `is_eq` of a scalar builtin (`F64`) is that
    /// builtin's `Prim`. Any other derived method is a `Derived` or the
    /// comparison of its backing, which no `Prim` names, so it is null.
    fn derivedMethodPrim(self: *Reifier, source: CIR.Expr.Idx) ?u128 {
        const foreign = self.walk.foreign;
        const target = foreign.resolve_lookup_target(foreign.context, source) orelse return null;
        const derived = switch (target.env.store.getExpr(target.env.store.getDef(target.def).expr)) {
            .e_derived_method => |derived| derived,
            .e_num,
            .e_frac_f32,
            .e_frac_f64,
            .e_dec,
            .e_dec_small,
            .e_num_from_numeral,
            .e_typed_int,
            .e_typed_frac,
            .e_typed_num_from_numeral,
            .e_str_segment,
            .e_str,
            .e_bytes_literal,
            .e_lookup_local,
            .e_lookup_external,
            .e_deferred_import_ref,
            .e_lookup_associated_local,
            .e_lookup_associated,
            .e_lookup_associated_resolved,
            .e_lookup_required,
            .e_list,
            .e_empty_list,
            .e_tuple,
            .e_match,
            .e_if,
            .e_call,
            .e_record,
            .e_empty_record,
            .e_block,
            .e_tag,
            .e_nominal,
            .e_nominal_external,
            .e_zero_argument_tag,
            .e_closure,
            .e_lambda,
            .e_binop,
            .e_unary_minus,
            .e_field_access,
            .e_method_call,
            .e_dispatch_call,
            .e_interpolation,
            .e_structural_eq,
            .e_structural_hash,
            .e_method_eq,
            .e_type_method_call,
            .e_type_dispatch_call,
            .e_tuple_access,
            .e_runtime_error,
            .e_crash,
            .e_dbg,
            .e_expect_err,
            .e_expect,
            .e_ellipsis,
            .e_anno_only,
            .e_return,
            .e_break,
            .e_for,
            .e_hosted_lambda,
            .e_run_low_level,
            => return null,
        };
        if (derived.kind != .equality) return null;
        const builtin_nominal = checked.checkedBuiltinNominalForSourceDecl(target.env, @backingInt(derived.owner)) orelse return null;
        if (!isScalarEq(builtin_nominal)) return null;
        return reify.identity.builtinPrim(primitiveOwnerText(builtin_nominal).?, "is_eq");
    }

    /// The bits of the `Code.TypeId` of the type the proxy `arg` of a
    /// `Code.type_id` call stands for, read off the argument's solved type.
    /// Null where that type is open or is no nominal.
    fn typeIdIdentity(self: *Reifier, arg: ExprId) ?u128 {
        // The proxy's type in the frame the walk reads: in a generic
        // function, what the closing use fixed it to (Q8).
        var ref: FramedType = .{ .reader = self, .id = self.proxyTarget(arg), .frame = self.frame };
        while (true) {
            if (ref.reader.fixedTypeIn(ref.frame, ref.id)) |fixed| {
                ref = fixed;
                continue;
            }
            switch (ref.reader.types.payload(ref.id)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .alias => |alias| ref.id = alias.backing,
                .nominal => |nominal| return ref.reader.typeIdentity(nominal),
                .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => return null,
            }
        }
    }

    /// The type `t` of the `Code.Proxy(t)` that the argument `arg` of a
    /// `Code.type_id` or `Code.ty_of` call is, as checking typed it.
    fn proxyTarget(self: *Reifier, arg: ExprId) CheckedTypeId {
        const proxy = switch (self.types.payload(self.throughAliases(self.bodies.valueType(arg)))) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .nominal => |nominal| nominal,
            .pending,
            .err,
            .flex,
            .rigid,
            .alias,
            .record,
            .tuple,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => invariant("the argument of Code.type_id or Code.ty_of is a Code.Proxy, as checking typed it"),
        };
        std.debug.assert(proxy.args.len == 1);
        return proxy.args[0];
    }

    /// The `Code.Ty` of a `Code.ty_of` call's proxy, as the `result` of
    /// `|x| x` at that type describes it, written into this module's store
    /// (D6). A type variable the frame leaves open is `ty_of_not_closed`;
    /// a type the walk has no description for is the walk's own refusal.
    fn tyOfProxy(self: *Reifier, arg: ExprId, region: base.Region) Allocator.Error!Outcome {
        self.walk.body = self;
        const ty = self.tyOf(self.proxyTarget(arg), region) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.Diverged => invariant("a type description diverged"),
            error.Rejected => {
                const rejection = self.walk.rejection.?;
                if (rejection.open == null) return .{ .rejected = rejection };
                return .{ .rejected = .{ .kind = .ty_of_not_closed, .region = region, .module = self.rejectionModule(), .detail = "" } };
            },
        };
        return .{ .reified = try self.walk.emitTy(ty) };
    }

    /// `id` with every alias at its head replaced by its backing.
    fn throughAliases(self: *Reifier, id: CheckedTypeId) CheckedTypeId {
        var current = id;
        while (true) switch (self.types.payload(current)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| current = alias.backing,
            .pending,
            .err,
            .flex,
            .rigid,
            .record,
            .tuple,
            .nominal,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => return current,
        };
    }

    /// The bits of the `Code.TypeId` of a nominal, as an `Opaque` of it
    /// carries them (`code_emit`).
    fn typeIdentity(self: *Reifier, nominal: checked.CheckedNominalType) u128 {
        if (self.isBuiltinNominal(nominal)) return reify.identity.builtinType(self.opaqueName(nominal));
        return reify.identity.declaredType(.{
            .module = self.names.moduleIdentityBytes(nominal.origin_module).*,
            .decl = nominal.source_decl,
        });
    }

    /// What a nominal is apart from its name (F2): a builtin, known by its
    /// declaring module and not by its name, or the declaration its declaring
    /// module makes, as `foreignNominal` names it to every module's
    /// registries. A package nominal with a builtin's name is a declaration.
    fn nominalOrigin(self: *Reifier, nominal: checked.CheckedNominalType) Allocator.Error!reify.types.Origin {
        if (self.isBuiltinNominal(nominal)) return .builtin;
        return self.rt().declared(.{
            .module = self.names.moduleIdentityBytes(nominal.origin_module).*,
            .decl = nominal.source_decl,
        });
    }

    /// A record type's fields, following its extension. A field is optional
    /// where the checker pinned it so or where the frame fixes its kind
    /// variable so (`fieldKindIn`); a defaulted field is filled in.
    fn recordTy(self: *Reifier, fields: checked.CheckedRecordFields, ext: ?CheckedTypeId, region: base.Region) Error!TyId {
        var collected = std.ArrayList(FieldRef).empty;
        defer collected.deinit(self.gpa);
        var bound = std.ArrayList(BoundNominal).empty;
        defer releaseBoundNominals(self.gpa, &bound);
        try self.collectRecordFields(&collected, &bound, fields, ext, region);
        const specs = try self.gpa.alloc(reify.types.FieldSpec, collected.items.len);
        defer self.gpa.free(specs);
        for (collected.items, specs) |field, *spec| {
            const optional = switch (field.reader.fieldKindIn(field.frame, field.field.kind)) {
                .required, .defaulted => false,
                .optional => true,
                .undetermined => invariant("a field kind read in its frame is determined"),
                .err => return self.rejectError(.unresolved_type, region, "a record field whose presence is an error"),
            };
            spec.* = .{
                .name = field.reader.names.recordFieldLabelText(field.field.name),
                .ty = try field.reader.tyOfIn(field.frame, field.field.ty, region),
                .optional = optional,
                .default = try field.reader.fieldDefault(field.field.kind),
            };
        }
        return self.rt().recordTy(specs);
    }

    /// The kind of a record field read in `frame` (design.md "Field
    /// Kinds"): its own kind, or, for a field whose kind is a quantified kind
    /// variable, the kind the frame's substitution fixed the variable to (a
    /// `field_kind` entry the checker published for the use). A kind
    /// variable no substitution fixes is `required`, the kind a
    /// specialization commits a still-undetermined kind to (Monotype's
    /// relation freeze), and so is a field the checker left undetermined.
    fn fieldKindIn(self: *Reifier, frame: FrameId, kind: checked.CheckedFieldKind) checked.CheckedFieldKind.Tag {
        if (kind.tag != .undetermined) return kind.tag;
        const variable = kind.undeterminedVariable() orelse invariant("an undetermined field kind names no kind variable");
        const fixed = self.fixedTypeIn(frame, variable) orelse return .required;
        return switch (fixed.reader.types.payload(fixed.id)) {
            .field_kind => |committed| switch (committed) {
                .required => .required,
                .optional => .optional,
            },
            // A kind variable of the caller's own scheme that nothing fixes.
            .flex, .rigid => .required,
            .pending, .err, .alias, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => invariant("a kind variable is fixed to a type"),
        };
    }

    /// What a field's type says about its default (D5): its value where the
    /// walk describes the default as a literal, or an aggregate, tag or
    /// nominal of literals, and `computed` for any other default. The
    /// default is read in the module that declares it, by the identity the
    /// field's kind carries.
    fn fieldDefault(self: *Reifier, kind: checked.CheckedFieldKind) Allocator.Error!reify.types.Default {
        const identity = kind.defaultIdentity() orelse return .none;
        const origin = identity.origin() orelse invariant("a defaulted field names the module that declares its default");
        const holder = try self.moduleOfIdentity(self.names.moduleIdentityBytes(origin));
        const expr = holder.bodies.defaultExpr(identity.expr_node) orelse
            invariant("the module that declares a field default archives its expression");
        // A default is a closed expression, typed on its own: no frame of
        // the walk names its variables.
        const outer_frame = holder.frame;
        holder.frame = empty_frame;
        defer holder.frame = outer_frame;
        const value = try holder.defaultValue(expr, .own) orelse return .computed;
        return .of(value);
    }

    /// The reader of the module of content identity `identity`: one the
    /// walk has open, or one in reach of the module being published.
    fn moduleOfIdentity(self: *Reifier, identity: *const [32]u8) Allocator.Error!*Reifier {
        for (self.walk.readers.items) |open| {
            const own = open.env.contentIdentityHash() orelse continue;
            if (base.ModuleIdentity.eql(own, identity)) return open;
        }
        const module = self.walk.foreign.findModuleByIdentity(identity) orelse
            invariant("the module that declares a field default is in reach of every module that reads the field");
        return self.walk.reader(module);
    }

    /// Where a default's expression stands, as the walk builds it: at its
    /// own type, as the backing of a `Bool`, or as the backing of another
    /// nominal, which the nominal wraps (`nominalExpr`).
    const DefaultPlace = enum { own, bool_backing, nominal_backing };

    /// What a checked type is, for the value of a default: the walk's type
    /// classes (`nominalTy`), read without building the type.
    const ValueClass = enum { bool_, str, scalar, list, record, tuple, tag_union, wrap, other };

    fn valueClass(self: *Reifier, type_id: CheckedTypeId) ValueClass {
        return switch (self.types.payload(self.throughAliases(type_id))) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .nominal => |nominal| if (nominal.builtin) |builtin| switch (builtin) {
                .bool => .bool_,
                .str => .str,
                .dec, .f32, .f64, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => .scalar,
                .list => .list,
                .try_ => .wrap,
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
                => .other,
            } else if (self.readsOpaque(nominal) or self.types.nominalBackingTemplateForPayload(nominal) == null) .other else .wrap,
            .record, .empty_record => .record,
            .tuple => .tuple,
            .tag_union, .empty_tag_union => .tag_union,
            .pending, .err, .alias, .flex, .rigid, .function => .other,
        };
    }

    /// The `Code.Value` of a field default that the walk describes as a
    /// literal (D5), or null for one it describes otherwise: a call, a
    /// literal of a type of the author's own (its conversion call), a
    /// constant of an opaque type (a `Prim`), a value of an opaque type, or
    /// a record that leaves out a field. A record that leaves out an
    /// optional field is null too: a field default does not use
    /// `Code.Value.Absent`, which only a captured value holds (D8).
    fn defaultValue(self: *Reifier, expr_id: ExprId, place: DefaultPlace) Allocator.Error!?reify.types.ValueId {
        const types = self.rt();
        const expr = self.bodies.expr(expr_id);
        switch (expr.data) {
            .numeral => {
                const primitive = self.builtinNominalOf(expr.ty) orelse return null;
                const exact = self.env.exactNumeral(self.bodies.numeralLiteral(@backingInt(expr_id)));
                return switch (primitive) {
                    .f32 => try types.fracValue(@bitCast(@as(f64, try numeral.floatBits(f32, self.gpa, exact)))),
                    .f64 => try types.fracValue(@bitCast(try numeral.floatBits(f64, self.gpa, exact))),
                    .dec => if (try numeral.decBits(self.gpa, exact)) |bits| try types.decValue(bits) else null,
                    .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => blk: {
                        const bits = numeral.intBits(exact, intTarget(primitive).?) orelse break :blk null;
                        // `Code.Value` is `U128` for a `U128` and `Int` for every other width.
                        if (primitive == .u128) break :blk try types.u128Value(switch (bits) {
                            .i128 => |signed| @intCast(signed),
                            .u128 => |magnitude| magnitude,
                        });
                        break :blk try types.intValue(switch (bits) {
                            .i128 => |signed| signed,
                            .u128 => |magnitude| @intCast(magnitude),
                        });
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
                    => null,
                };
            },
            .str_segment => |literal| return try types.strValue(self.bodies.text(literal)),
            .str => |segments| {
                const raw = @backingInt(expr_id);
                var text = std.ArrayList(u8).empty;
                defer text.deinit(self.gpa);
                // A quote converted to a type of the author's own is its
                // `from_quote` call, which is no literal default.
                if (self.bodies.quoteIsCustom(raw)) {
                    if (self.builtinNominalOf(expr.ty) != .str) return null;
                    try self.bodies.appendText(self.gpa, self.bodies.quoteText(raw), &text);
                    return try types.strValue(text.items);
                }
                for (segments) |segment| switch (self.bodies.exprData(segment)) {
                    .str_segment => |literal| try text.appendSlice(self.gpa, self.bodies.text(literal)),
                    .numeral,
                    .code_site,
                    .str,
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
                    => return null,
                };
                return try types.strValue(text.items);
            },
            .bytes_literal => |literal| return try types.bytesValue(self.bodies.text(literal)),
            .empty_list => return try types.listValue(&.{}),
            .list, .tuple => |parts| {
                const items = try self.defaultValues(parts) orelse return null;
                defer self.gpa.free(items);
                return if (expr.data == .list) try types.listValue(items) else try types.tupleValue(items);
            },
            .empty_record => return try types.recordValue(&.{}),
            .record => |record| {
                // A record that unsets a field or leaves out an optional
                // field is not a literal default: a default does not use
                // `Code.Value.Absent` (D8). A field left out with a default
                // the type carries is that default (Q18).
                if (record.ext != null or record.unsets.len != 0) return null;
                var fields = std.ArrayList(checked.CheckedRecordField).empty;
                defer fields.deinit(self.gpa);
                if (!try self.recordTypeFields(expr.ty, &fields)) return null;
                std.mem.sort(checked.CheckedRecordField, fields.items, self, struct {
                    fn lt(r: *Reifier, a: checked.CheckedRecordField, b: checked.CheckedRecordField) bool {
                        return r.names.recordFieldLabelTextLessThan(a.name, b.name);
                    }
                }.lt);
                const items = try self.gpa.alloc(reify.types.ValueId, fields.items.len);
                defer self.gpa.free(items);
                for (fields.items, items) |field, *item| {
                    const written = for (record.fields) |candidate_id| {
                        const candidate = self.bodies.recordField(candidate_id);
                        if (candidate.label == field.name) break candidate.value;
                    } else null;
                    if (written) |value_expr| {
                        item.* = try self.defaultValue(value_expr, .own) orelse return null;
                    } else {
                        item.* = (try self.fieldDefault(field.kind)).value() orelse return null;
                    }
                }
                const value = try types.recordValue(items);
                return if (place == .own and self.valueClass(expr.ty) == .wrap) try types.wrapValue(value) else value;
            },
            .tag => |tag_expr| return self.tagValue(self.bodies.tagLabel(tag_expr.name), tag_expr.args, expr.ty, place),
            .zero_argument_tag => |tag_expr| return self.tagValue(self.bodies.tagLabel(tag_expr.name), &.{}, expr.ty, place),
            .nominal => |nominal| return switch (self.valueClass(expr.ty)) {
                .bool_ => self.defaultValue(nominal.backing_expr, .bool_backing),
                .wrap => blk: {
                    const backing = try self.defaultValue(nominal.backing_expr, .nominal_backing) orelse break :blk null;
                    break :blk try types.wrapValue(backing);
                },
                .str, .scalar, .list => self.defaultValue(nominal.backing_expr, .nominal_backing),
                // A value of an opaque type, built from its fields.
                .record, .tuple, .tag_union, .other => null,
            },
            // A name is the value the definition it names holds, unless the
            // walk names it as a primitive: a constant of an opaque type.
            .lookup_local, .lookup_external, .lookup_required => return self.namedDefaultValue(self.bodies.resolvedRef(expr_id), place),
            .code_site,
            .match_,
            .if_,
            .call,
            .block,
            .closure,
            .lambda,
            .binop,
            .unary_minus,
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
            => return null,
        }
    }

    fn defaultValues(self: *Reifier, parts: []const ExprId) Allocator.Error!?[]reify.types.ValueId {
        const items = try self.gpa.alloc(reify.types.ValueId, parts.len);
        errdefer self.gpa.free(items);
        for (parts, items) |part, *item| {
            item.* = try self.defaultValue(part, .own) orelse {
                self.gpa.free(items);
                return null;
            };
        }
        return items;
    }

    /// A tag in a default: a `Bool`, a variant, or a variant wrapped in the
    /// nominal its type is (`tagExpr`).
    fn tagValue(self: *Reifier, name: canonical.TagLabelId, args: []const ExprId, ty: CheckedTypeId, place: DefaultPlace) Allocator.Error!?reify.types.ValueId {
        const types = self.rt();
        const class = self.valueClass(ty);
        if (place == .bool_backing or (place == .own and class == .bool_)) {
            const flag = self.bool_tags.value(name) orelse return null;
            return try types.boolValue(flag);
        }
        switch (class) {
            .wrap, .tag_union => {},
            .bool_, .str, .scalar, .list, .record, .tuple, .other => return null,
        }
        const payloads = try self.defaultValues(args) orelse return null;
        defer self.gpa.free(payloads);
        const variant = try types.tagValue(self.names.tagLabelText(name), payloads);
        return if (place == .own and class == .wrap) try types.wrapValue(variant) else variant;
    }

    /// The default value of the definition a name holds (`foldedConstant`).
    fn namedDefaultValue(self: *Reifier, resolved: ?checked.ResolvedValueRefId, place: DefaultPlace) Allocator.Error!?reify.types.ValueId {
        const definition = try self.constantDefinition(resolved) orelse return null;
        const reader = definition.reader;
        if (definition.named) |named| {
            if (try reader.primitiveOf(named.def, named.ty)) |primitive| switch (primitive) {
                .operation => return null,
                .builtin => invariant("a constant of the builtin module is no primitive"),
            };
        }
        if (reader.folding.contains(definition.body)) return null;
        try reader.folding.put(reader.gpa, definition.body, {});
        defer _ = reader.folding.remove(definition.body);
        const outer_frame = reader.frame;
        reader.frame = empty_frame;
        defer reader.frame = outer_frame;
        return reader.defaultValue(definition.body, place);
    }

    /// The fields of a closed record type, or of the record a nominal is
    /// backed by, into `out`; false for an open one.
    fn recordTypeFields(self: *Reifier, type_id: CheckedTypeId, out: *std.ArrayList(checked.CheckedRecordField)) Allocator.Error!bool {
        var current = type_id;
        while (true) switch (self.types.payload(current)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| current = alias.backing,
            .nominal => |nominal| current = self.types.nominalBackingTemplateForPayload(nominal) orelse return false,
            .record => |record| {
                try record.fields.appendTo(self.gpa, out);

                current = record.ext;
            },
            .empty_record => return true,
            // A row tail nothing pins is sealed to the empty record.
            .flex => |variable| return self.types.payload(current).variableSealsToRowDefault() and variable.row_default.? == .empty_record,
            .pending, .err, .rigid, .tuple, .function, .tag_union, .empty_tag_union => return false,
        };
    }

    /// The bindings a record-backed nominal in a record's extension chain
    /// made for its declared variables. They stay bound while the caller reads
    /// the collected field types, which are written in those variables.
    const BoundNominal = struct {
        reader: *Reifier,
        args: NominalArgs,
    };

    /// Put back the bindings of every nominal an extension chain opened, the
    /// last opened first.
    fn releaseBoundNominals(gpa: Allocator, bound: *std.ArrayList(BoundNominal)) void {
        while (bound.pop()) |entry| {
            var args = entry.args;
            entry.reader.releaseNominalArgs(&args);
        }
        bound.deinit(gpa);
    }

    /// Every field of a record type, following its extension.
    ///
    /// A chain ending in a variable the site fixed carries on in the site's
    /// module: the definition wrote the fields it named and the site's record
    /// holds the rest. That record holds the named fields too, so a field
    /// already collected is dropped where it comes round a second time.
    ///
    /// A record-backed `:=` nominal in the chain contributes its backing's
    /// fields at this use's arguments, as Monotype's `flattenRecordRow` reads
    /// it: its name is not kept (design.md "Record Extension
    /// Well-Formedness").
    fn collectRecordFields(
        self: *Reifier,
        collected: *std.ArrayList(FieldRef),
        opened: *std.ArrayList(BoundNominal),
        fields: checked.CheckedRecordFields,
        ext: ?CheckedTypeId,
        region: base.Region,
    ) Error!void {
        var reader = self;
        var frame = self.frame;
        var link_fields = fields;
        var link_ext = ext;
        while (true) {
            var link = link_fields.iterator();
            while (link.next()) |field| try self.collectField(collected, reader, frame, field);
            const next = link_ext orelse break;
            switch (reader.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .empty_record => break,
                .record => |record| {
                    link_fields = record.fields;
                    link_ext = record.ext;
                },
                .alias => |alias| {
                    link_fields = .empty;
                    link_ext = alias.backing;
                },
                .flex, .rigid => |variable| {
                    const bound = reader.fixedTypeIn(frame, next) orelse {
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
                    frame = bound.frame;
                    link_fields = .empty;
                    link_ext = bound.id;
                },
                .nominal => |nominal| {
                    // The checker admits only a record-backed `:=` nominal
                    // here (design.md "Record Extension Well-Formedness").
                    std.debug.assert(nominal.builtin == null and !nominal.is_opaque);
                    const backing = reader.types.nominalBackingTemplateForPayload(nominal) orelse unreachable; // a `:=` nominal a program declared has a backing
                    try opened.ensureUnusedCapacity(self.gpa, 1);
                    opened.appendAssumeCapacity(.{ .reader = reader, .args = try reader.bindNominalArgs(frame, nominal) });
                    link_fields = .empty;

                    link_ext = backing;
                },
                .pending, .err => return self.rejectError(.unresolved_type, region, "an unresolved type"),
                .tuple,
                .function,
                .tag_union,
                .empty_tag_union,
                => unreachable, // the checker refuses every other type in an extension slot (design.md "Record Extension Well-Formedness")
            }
        }
    }

    /// Put `fields` in label order, the order of a record's fields in
    /// `Code.Ty` and in Monotype (`addRecordFields`). The links of a checked
    /// row can name the fields in another order, so a derivation that walks
    /// the fields one by one sorts them first: it compares and hashes them
    /// in the compiler's order, whatever links the checker made.
    fn sortFieldsByLabel(fields: []FieldRef) void {
        std.mem.sort(FieldRef, fields, {}, fieldLabelLessThan);
    }

    /// Whether the label of `a` comes before the label of `b` in the
    /// compiler's label order (`Ident.textOrder`). Labels of one store
    /// compare by that store's rank. Two stores intern independently, so
    /// labels of two stores compare by their texts in that order.
    fn fieldLabelLessThan(_: void, a: FieldRef, b: FieldRef) bool {
        if (a.reader == b.reader) return a.reader.names.recordFieldLabelTextLessThan(a.field.name, b.field.name);
        return base.Ident.textLessThan(a.reader.names.recordFieldLabelText(a.field.name), b.reader.names.recordFieldLabelText(b.field.name));
    }

    /// `fieldLabelLessThan` for the variants of a tag union.
    fn tagLabelLessThan(_: void, a: VariantRef, b: VariantRef) bool {
        if (a.reader == b.reader) return a.reader.names.tagLabelTextLessThan(a.tag.name, b.tag.name);
        return base.Ident.textLessThan(a.reader.names.tagLabelText(a.tag.name), b.reader.names.tagLabelText(b.tag.name));
    }

    /// Collect one field, unless a link nearer the front of the chain already
    /// named it.
    fn collectField(self: *Reifier, collected: *std.ArrayList(FieldRef), reader: *Reifier, frame: FrameId, field: checked.CheckedRecordField) Allocator.Error!void {
        for (collected.items) |seen| {
            if (seen.reader.sameFieldLabel(seen.field.name, reader, field.name)) return;
        }
        try collected.append(self.gpa, .{ .reader = reader, .frame = frame, .field = field });
    }

    /// Refuse a `Code` value met inside a walked body, naming the constant the
    /// walk was folding when it met it (D7).
    fn rejectCodeValue(self: *Reifier, region: base.Region) error{Rejected} {
        return self.rejectError(.code_value, region, self.walk.constant orelse "");
    }

    fn rejectError(self: *Reifier, kind: Rejection.Kind, region: base.Region, detail: []const u8) error{Rejected} {
        if (self.walk.rejection == null) {
            self.walk.rejection = .{ .kind = kind, .region = region, .module = self.walk.bodyModule(), .detail = detail };
        }
        return error.Rejected;
    }

    /// This reader's module, as a refusal names it.
    fn rejectionModule(self: *const Reifier) Rejection.Module {
        return .{ .artifact = self.artifact, .env = self.env };
    }

    /// Make this reader's module the one whose source the walk reads, so a
    /// refusal from here on is placed in it. The caller restores the result
    /// with `leave` when it is done with this module's source.
    fn enter(self: *Reifier) ?*Reifier {
        const outer = self.walk.body;
        self.walk.body = self;
        return outer;
    }

    fn leave(self: *Reifier, outer: ?*Reifier) void {
        self.walk.body = outer;
    }

    /// Refuse a type variable, naming it and the place in the signature it
    /// stands in. A variable reached through a substitution is named by the
    /// quantified variable the annotation wrote, and the use left it open.
    fn rejectOpen(self: *Reifier, type_id: CheckedTypeId, region: base.Region) error{Rejected} {
        const named = self.walk.through orelse FramedType{ .reader = self, .id = type_id, .frame = self.frame };
        const variable = switch (named.reader.types.payload(named.id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .rigid => .use_leaves_open,
            .flex => |own_variable| if (own_variable.name != null) .use_leaves_open else .inferred_use_leaves_open,
            .pending, .err, .alias, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => invariant("a type variable was refused at a type that is not a variable"),
        } else if (own == .rigid)
            .annotation_leaves_open
        else
            .inferred;
        const at, const module, const place: OpenVariable.Place = switch (self.walk.place) {
            .expression => .{ region, self.walk.bodyModule(), .expression },
            .result => .{ region, self.walk.bodyModule(), .result },
            .parameter => |param| blk: {
                const pattern = param.reader.bodies.pattern(param.pattern);
                const single = pattern.data == .assign or pattern.data == .as;
                break :blk .{ pattern.source_region, param.reader.rejectionModule(), .{ .parameter = if (single)
                    .{ .name = param.reader.binderName(param.pattern) }
                else
                    .{ .position = param.position + 1 } } };
            },
        };
        if (self.walk.rejection == null) {
            self.walk.rejection = .{
                .kind = .unresolved_type,
                .region = at,
                .module = module,
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .nominal => |nominal| nominal,
            .alias => |alias| self.nominalOf(alias.backing),
            .pending, .err, .flex, .rigid, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The elements a checked id is a tuple of, reading through an alias.
    fn tupleOf(self: *Reifier, type_id: CheckedTypeId) ?[]const CheckedTypeId {
        return switch (self.types.payload(type_id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .tuple => |elements| elements,
            .alias => |alias| self.tupleOf(alias.backing),
            .pending, .err, .flex, .rigid, .record, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The builtin a checked type is, through an alias and through what the
    /// instantiation fixed a variable to.
    fn builtinNominalOf(self: *Reifier, type_id: CheckedTypeId) ?checked.CheckedBuiltinNominal {
        const resolved = self.resolvedType(type_id);
        if (resolved.reader != self) return resolved.reader.builtinNominalOf(resolved.id);
        return switch (self.types.payload(resolved.id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| self.builtinNominalOf(alias.backing),
            .nominal => |nominal| nominal.builtin,
            .flex, .rigid => |variable| if (self.unfit.contains(resolved.id)) null else if (defaultedVariable(variable)) |sealed| defaultBuiltin(sealed) else null,
            .pending, .err, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => null,
        };
    }

    /// The builtin module a checked type's methods belong to, as `Builtin.roc`
    /// exports it, when the type is a scalar builtin.
    fn primitiveOwner(self: *Reifier, type_id: CheckedTypeId) ?[]const u8 {
        return primitiveOwnerText(self.builtinNominalOf(type_id) orelse return null);
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
        use_expr: ?ExprId,
        region: base.Region,
        unfixed: Unfixed,
    ) Error!?Instantiation {
        const scheme_vars = scheme.vars;
        if (scheme_vars.len == 0) return null;
        // A lambda the checker generalized where it is written is its own
        // use: the checker recorded what that place copied its variables to
        // (`siteSubstitution` of the lambda), and gives no type to match.
        const recorded = if (use_expr) |expr| caller.plans.siteSubstitution(expr) != null else false;
        if (fixed == null and !recorded) {
            // A use that fixes no type leaves a hole only where the scheme
            // quantifies something other than a row (`rowVars`).
            var rows = try self.rowVars(scheme.root);
            defer rows.deinit(self.gpa);
            for (scheme_vars) |scheme_var| {
                if (!rows.contains(scheme_var)) return self.rejectError(.unresolved_type, region, unfixed.missing);
            }
            return null;
        }

        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        if (fixed) |payload| try self.matchType(&substitution, scheme_vars, scheme.root, caller.resolvedType(payload));

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

        return try self.closedInstantiation(scheme, &substitution, region, unfixed);
    }

    /// What a type occurrence of a descriptor method's owner fixes the
    /// variables of the template the method runs to (Q17): the template's
    /// parameter `param` the owner fills, matched to the owner type `owner`.
    /// Null when the template has none.
    fn instantiationAtOwner(self: *Reifier, scheme: Scheme, param: CheckedTypeId, owner: FramedType, region: base.Region) Error!?Instantiation {
        if (scheme.vars.len == 0) return null;
        var substitution: Substitution = .empty;
        errdefer substitution.deinit(self.gpa);
        try self.matchType(&substitution, scheme.vars, param, owner);
        return try self.closedInstantiation(scheme, &substitution, region, Unfixed.call);
    }

    /// `substitution` as an instantiation of `scheme`, which then owns it,
    /// or the refusal of a variable it leaves unbound.
    fn closedInstantiation(self: *Reifier, scheme: Scheme, substitution: *Substitution, region: base.Region, unfixed: Unfixed) Error!?Instantiation {
        const scheme_vars = scheme.vars;
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
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
                    .module = self.walk.bodyModule(),
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
        return .{ .substitution = substitution.*, .key = try instantiationKey(substitution.*, scheme_vars) };
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

    const RowVars = MentionVars;

    fn collectRowVars(self: *Reifier, found: *RowVars, seen: *RowVars, id: CheckedTypeId) Allocator.Error!void {
        if ((try seen.getOrPut(self.gpa, id)).found_existing) return;
        switch (self.types.payload(id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
                var fields = record.fields.iterator();
                while (fields.next()) |field| try self.collectRowVars(found, seen, field.ty);
                try self.collectRowTail(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                var tags = union_ty.tags.iterator();
                while (tags.next()) |variant| {
                    for (variant.args) |arg| try self.collectRowVars(found, seen, arg);
                }
                try self.collectRowTail(found, seen, union_ty.ext);
            },
            // A `where` obligation is part of the scheme, and a row its
            // method's type stands on is a row of the scheme too.
            .flex, .rigid => |variable| {
                var constraints = variable.constraints.iterator();
                while (constraints.next()) |constraint| try self.collectRowVars(found, seen, constraint.fn_ty);
            },
            .empty_record, .empty_tag_union, .pending, .err => {},
        }
    }

    /// Follow one extension chain to what it ends at, which is the row.
    fn collectRowTail(self: *Reifier, found: *RowVars, seen: *RowVars, id: CheckedTypeId) Allocator.Error!void {
        switch (self.types.payload(id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| try self.collectRowTail(found, seen, alias.backing),
            .record => |record| {
                var fields = record.fields.iterator();
                while (fields.next()) |field| try self.collectRowVars(found, seen, field.ty);
                try self.collectRowTail(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                var tags = union_ty.tags.iterator();
                while (tags.next()) |variant| {
                    for (variant.args) |arg| try self.collectRowVars(found, seen, arg);
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
        use: FramedType,
    ) Allocator.Error!void {
        for (scheme_vars) |scheme_var| {
            if (scheme_var != scheme_id) continue;
            if (!substitution.contains(scheme_id)) try substitution.put(self.gpa, scheme_id, use);
            return;
        }
        switch (self.types.payload(scheme_id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| try self.matchType(substitution, scheme_vars, alias.backing, use),
            .function => |scheme_fn| {
                const use_fn = use.reader.functionOf(use.id) orelse return;
                if (use_fn.args.len != scheme_fn.args.len) return;
                for (scheme_fn.args, use_fn.args) |arg, fixed| {
                    try self.matchType(substitution, scheme_vars, arg, use.reader.resolvedTypeIn(use.frame, fixed));
                }
                try self.matchType(substitution, scheme_vars, scheme_fn.ret, use.reader.resolvedTypeIn(use.frame, use_fn.ret));
            },
            .nominal => |scheme_nominal| {
                const use_nominal = use.reader.nominalOf(use.id) orelse return;
                if (use_nominal.args.len != scheme_nominal.args.len) return;
                for (scheme_nominal.args, use_nominal.args) |arg, fixed| {
                    try self.matchType(substitution, scheme_vars, arg, use.reader.resolvedTypeIn(use.frame, fixed));
                }
            },
            .tuple => |scheme_elements| {
                const use_elements = use.reader.tupleOf(use.id) orelse return;
                if (use_elements.len != scheme_elements.len) return;
                for (scheme_elements, use_elements) |element, fixed| {
                    try self.matchType(substitution, scheme_vars, element, use.reader.resolvedTypeIn(use.frame, fixed));
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
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
        fields: checked.CheckedRecordFields,
        ext: ?CheckedTypeId,
        use: FramedType,
    ) Allocator.Error!void {
        var scheme_fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer scheme_fields.deinit(self.gpa);
        try self.recordFields(&scheme_fields, fields, ext);

        var use_fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer use_fields.deinit(self.gpa);
        switch (use.reader.types.payload(use.id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .record => |use_record| try use.reader.recordFields(&use_fields, use_record.fields, use_record.ext),
            // A use written through an alias is its backing (D2).
            .alias => |alias| return self.matchRecord(substitution, scheme_vars, fields, ext, use.reader.resolvedTypeIn(use.frame, alias.backing)),
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
                try self.matchType(substitution, scheme_vars, field.ty, use.reader.resolvedTypeIn(use.frame, fixed.ty));
                break;
            }
        }

        // The row the scheme stands on is the fields the use has beyond the
        // ones the scheme named, and `Ty.Record` is a closed list, so the walk
        // needs them. The use's whole record is what it binds to: the residual
        // is no type the artifact holds. A walk drops a field a nearer link
        // already named, and an owner term binds the variable to exactly the
        // rest (`TableBuilder.ownerTerm`).
        const row = self.recordRowTail(ext) orelse return;
        for (scheme_vars) |scheme_var| {
            if (scheme_var != row) continue;
            if (!substitution.contains(row)) try substitution.put(self.gpa, row, use);
            return;
        }
    }

    /// The labels that the links of each row of `id` name above the row
    /// variable `variable`, for each row that ends at it (Q17, an owner
    /// term's row binding). A label can repeat.
    fn nearerRowLabels(
        self: *Reifier,
        id: CheckedTypeId,
        variable: CheckedTypeId,
        fields: *std.ArrayList(canonical.RecordFieldLabelId),
        tags: *std.ArrayList(canonical.TagLabelId),
    ) Allocator.Error!void {
        var seen: RowVars = .empty;
        defer seen.deinit(self.gpa);
        var work = std.ArrayList(CheckedTypeId).empty;
        defer work.deinit(self.gpa);
        var chain_fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer chain_fields.deinit(self.gpa);
        var chain_tags = std.ArrayList(checked.CheckedTag).empty;
        defer chain_tags.deinit(self.gpa);
        try work.append(self.gpa, id);
        while (work.pop()) |current| {
            if ((try seen.getOrPut(self.gpa, current)).found_existing) continue;
            switch (self.types.payload(current)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .flex, .rigid => |flex| {
                    var constraints = flex.constraints.iterator();
                    while (constraints.next()) |constraint| try work.append(self.gpa, constraint.fn_ty);
                },
                .alias => |alias| try work.append(self.gpa, alias.backing),
                .function => |fn_ty| {
                    try work.appendSlice(self.gpa, fn_ty.args);
                    try work.append(self.gpa, fn_ty.ret);
                },
                .nominal => |nominal| try work.appendSlice(self.gpa, nominal.args),
                .tuple => |parts| try work.appendSlice(self.gpa, parts),
                .record => |record| {
                    var record_fields = record.fields.iterator();
                    while (record_fields.next()) |field| {
                        if (field.kind.undeterminedVariable()) |kind| try work.append(self.gpa, kind);
                        try work.append(self.gpa, field.ty);
                    }
                    try work.append(self.gpa, record.ext);
                    if (self.recordRowTail(record.ext) == variable) {
                        chain_fields.clearRetainingCapacity();
                        try self.recordFields(&chain_fields, record.fields, record.ext);
                        for (chain_fields.items) |field| try fields.append(self.gpa, field.name);
                    }
                },
                .tag_union => |union_ty| {
                    var union_tags = union_ty.tags.iterator();
                    while (union_tags.next()) |variant| try work.appendSlice(self.gpa, variant.args);
                    try work.append(self.gpa, union_ty.ext);
                    if (self.tagRowTail(union_ty.ext) == variable) {
                        chain_tags.clearRetainingCapacity();
                        try self.unionTags(&chain_tags, union_ty.tags, union_ty.ext);
                        for (chain_tags.items) |tag| try tags.append(self.gpa, tag.name);
                    }
                },
                .empty_record, .empty_tag_union, .pending, .err => {},
            }
        }
    }

    /// Whether a row's extension chain from `ext` ends at an empty record
    /// or an empty tag union: the row is closed.
    fn rowEndIsEmpty(self: *Reifier, ext: CheckedTypeId) bool {
        var link = ext;
        while (true) {
            switch (self.types.payload(link)) {
                .record => |record| link = record.ext,
                .tag_union => |more| link = more.ext,
                .alias => |alias| link = alias.backing,
                .empty_record, .empty_tag_union => return true,
                .field_kind, .flex, .rigid, .pending, .err, .tuple, .nominal, .function => return false,
            }
        }
    }

    /// The variable one record type stands its row on, or null where its
    /// extension chain ends closed.
    fn recordRowTail(self: *Reifier, ext: ?CheckedTypeId) ?CheckedTypeId {
        var link = ext orelse return null;
        while (true) {
            switch (self.types.payload(link)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
        fields: checked.CheckedRecordFields,
        ext: ?CheckedTypeId,
    ) Allocator.Error!void {
        var link_fields = fields;
        var link_ext = ext;
        while (true) {
            try link_fields.appendTo(self.gpa, into);
            const next = link_ext orelse break;
            switch (self.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .record => |record| {
                    link_fields = record.fields;
                    link_ext = record.ext;
                },
                .alias => |alias| {
                    link_fields = .empty;
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
        tags: checked.CheckedTags,
        ext: CheckedTypeId,
        use: FramedType,
    ) Allocator.Error!void {
        var scheme_tags = std.ArrayList(checked.CheckedTag).empty;
        defer scheme_tags.deinit(self.gpa);
        try self.unionTags(&scheme_tags, tags, ext);

        var use_tags = std.ArrayList(checked.CheckedTag).empty;
        defer use_tags.deinit(self.gpa);
        switch (use.reader.types.payload(use.id)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
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
                const payloads = variant.args;
                const fixed_payloads = fixed.args;
                if (payloads.len != fixed_payloads.len) break;
                for (payloads, fixed_payloads) |payload, fixed_payload| {
                    try self.matchType(substitution, scheme_vars, payload, use.reader.resolvedTypeIn(use.frame, fixed_payload));
                }
                break;
            }
        }

        // The row the scheme stands on is the variants the use has beyond the
        // ones the scheme named, bound to the use's whole union as a record's
        // row is (`matchRecord`): `collectVariants` drops a variant a nearer
        // link already named, and an owner term binds the variable to
        // exactly the rest (`TableBuilder.ownerTerm`).
        const row = self.tagRowTail(ext) orelse return;
        for (scheme_vars) |scheme_var| {
            if (scheme_var != row) continue;
            if (!substitution.contains(row)) try substitution.put(self.gpa, row, use);
            return;
        }
    }

    /// The variable one tag union type stands its row on, or null where its
    /// extension chain ends closed.
    fn tagRowTail(self: *Reifier, ext: CheckedTypeId) ?CheckedTypeId {
        var link = ext;
        while (true) {
            switch (self.types.payload(link)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .flex, .rigid => return link,
                .tag_union => |more| link = more.ext,
                .alias => |alias| link = alias.backing,
                .pending,
                .err,
                .tuple,
                .nominal,
                .function,
                .record,
                .empty_record,
                .empty_tag_union,
                => return null,
            }
        }
    }

    /// The variants a tag union has, following its extension.
    fn unionTags(
        self: *Reifier,
        into: *std.ArrayList(checked.CheckedTag),
        tags: checked.CheckedTags,
        ext: CheckedTypeId,
    ) Allocator.Error!void {
        var link_tags = tags;
        var link_ext: ?CheckedTypeId = ext;
        while (true) {
            try link_tags.appendTo(self.gpa, into);
            const next = link_ext orelse break;
            switch (self.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .tag_union => |more| {
                    link_tags = more.tags;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_tags = .empty;

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

    /// Whether a type name of this store and a type name of another store
    /// are the same name, as `sameFieldLabel` does for field labels.
    fn sameTypeName(
        self: *Reifier,
        name: canonical.TypeNameId,
        other: *Reifier,
        other_name: canonical.TypeNameId,
    ) bool {
        if (self == other) return name == other_name;
        const here = other.names.lookupTypeName(self.names.typeNameText(name)) orelse return false;
        return here == other_name;
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
    ) Allocator.Error![32]u8 {
        var hasher = std.crypto.hash.Blake3.init(.{});
        for (scheme_vars) |scheme_var| {
            // An unbound variable is a row, which no description names, so
            // every use of this definition keys the same row for it.
            const bound = substitution.get(scheme_var) orelse {
                hasher.update(&@as([32]u8, @splat(0)));
                continue;
            };
            try hashBinding(&hasher, bound);
        }
        // A structure the use lifted into a nominal (`matchType`) is keyed
        // too, by the nominal it stands for: a use that lifts it and one that
        // does not are two types the definition is called at. The structure
        // is keyed by id: it is a node of the scheme every use reads, so one
        // position of the scheme has one id for every use. The entries are
        // in the order the match met them, which the scheme fixes.
        var entries = substitution.constIterator();
        while (entries.next()) |entry| {
            const in_scheme = for (scheme_vars) |scheme_var| {
                if (scheme_var == entry.key_ptr.*) break true;
            } else false;
            if (in_scheme) continue;
            hasher.update(std.mem.asBytes(&@backingInt(entry.key_ptr.*)));
            try hashBinding(&hasher, entry.value_ptr.*);
        }
        var key: [32]u8 = undefined;
        hasher.final(&key);
        return key;
    }

    /// Digest one binding: its type, and what each variable in that type
    /// stands for in the frame the binding names (D2). Two instances of an
    /// outer definition bind an inner row to one record id whose tail is the
    /// outer row, so the id alone would give both one key. A frame's bindings
    /// were made in earlier frames, so the descent ends.
    fn hashBinding(hasher: *std.crypto.hash.Blake3, bound: FramedType) Allocator.Error!void {
        if (try hashRecordBinding(hasher, bound)) return;
        if (try hashTagBinding(hasher, bound)) return;
        hasher.update(&(try bound.reader.types.rootKey(bound.id)).bytes);
        if (bound.frame == empty_frame) return;
        const reader = bound.reader;
        var variables = std.ArrayList(CheckedTypeId).empty;
        defer variables.deinit(reader.gpa);
        var seen: RowVars = .empty;
        defer seen.deinit(reader.gpa);
        try reader.collectVariables(&variables, &seen, bound.id);
        for (variables.items) |variable| {
            const fixed = reader.walk.frameSubstitution(bound.frame).get(variable) orelse continue;
            std.debug.assert(fixed.frame < bound.frame);
            try hashBinding(hasher, fixed);
        }
    }

    /// Digest a binding that is a record as the record its extension chain
    /// reaches through the frames: its fields by name, each once, the nearest
    /// link's first, and what the chain ends at. A recursive call of an
    /// open-row helper binds its row to its own parameter record, whose tail
    /// is the row the call above bound, so one type is written a new way at
    /// each depth. Digesting what the chain reaches gives every depth one key,
    /// and the walk meets the row it opened (D2). False when the binding is
    /// not a record.
    fn hashRecordBinding(hasher: *std.crypto.hash.Blake3, bound: FramedType) Allocator.Error!bool {
        var id = bound.id;
        while (bound.reader.types.payload(id) == .alias) id = bound.reader.types.payload(id).alias.backing;
        const record = switch (bound.reader.types.payload(id)) {
            // A substitution binds a quantified kind variable to a field kind.
            .field_kind => return false,
            .record => |record| record,
            .pending,
            .err,
            .flex,
            .rigid,
            .alias,
            .tuple,
            .nominal,
            .function,
            .empty_record,
            .tag_union,
            .empty_tag_union,
            => return false,
        };
        const gpa = bound.reader.gpa;
        var fields = std.ArrayList(FieldRef).empty;
        defer fields.deinit(gpa);
        var reader = bound.reader;
        var frame = bound.frame;
        var link_fields = record.fields;
        var link_ext: ?CheckedTypeId = record.ext;
        var tail: ?FramedType = null;
        while (true) {
            var link = link_fields.iterator();
            while (link.next()) |field| try reader.collectField(&fields, reader, frame, field);
            const next = link_ext orelse break;
            switch (reader.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .empty_record => break,
                .record => |more| {
                    link_fields = more.fields;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_fields = .empty;
                    link_ext = alias.backing;
                },
                .flex, .rigid => {
                    const fixed = reader.fixedTypeIn(frame, next) orelse {
                        tail = .{ .reader = reader, .id = next, .frame = frame };
                        break;
                    };
                    reader = fixed.reader;
                    frame = fixed.frame;
                    link_fields = .empty;
                    link_ext = fixed.id;
                },
                .nominal, .tuple, .function, .tag_union, .empty_tag_union, .pending, .err => {
                    tail = .{ .reader = reader, .id = next, .frame = frame };
                    break;
                },
            }
        }
        std.mem.sort(FieldRef, fields.items, {}, fieldLabelLessThan);
        hasher.update("record");
        for (fields.items) |field| {
            const label = field.reader.names.recordFieldLabelText(field.field.name);
            hasher.update(std.mem.asBytes(&label.len));
            hasher.update(label);
            hasher.update(std.mem.asBytes(&@backingInt(field.reader.fieldKindIn(field.frame, field.field.kind))));
            try hashBinding(hasher, field.reader.resolvedTypeIn(field.frame, field.field.ty));
        }
        if (tail) |end| try hashBinding(hasher, end) else hasher.update("closed");
        return true;
    }

    /// `hashRecordBinding` for a tag union: its variants by name, each once,
    /// the nearest link's first, and what the chain ends at. A recursive call
    /// of an open-row helper over a tag union binds its row the same way a
    /// record helper does (D2). False when the binding is not a tag union.
    fn hashTagBinding(hasher: *std.crypto.hash.Blake3, bound: FramedType) Allocator.Error!bool {
        var id = bound.id;
        while (bound.reader.types.payload(id) == .alias) id = bound.reader.types.payload(id).alias.backing;
        const tag_union = switch (bound.reader.types.payload(id)) {
            // A substitution binds a quantified kind variable to a field kind.
            .field_kind => return false,
            .tag_union => |tag_union| tag_union,
            .pending,
            .err,
            .flex,
            .rigid,
            .alias,
            .record,
            .tuple,
            .nominal,
            .function,
            .empty_record,
            .empty_tag_union,
            => return false,
        };
        const gpa = bound.reader.gpa;
        var variants = std.ArrayList(VariantRef).empty;
        defer variants.deinit(gpa);
        var reader = bound.reader;
        var frame = bound.frame;
        var link_tags = tag_union.tags;
        var link_ext: ?CheckedTypeId = tag_union.ext;
        var tail: ?FramedType = null;
        while (true) {
            var link = link_tags.iterator();
            while (link.next()) |tag| try reader.collectVariant(&variants, reader, frame, tag);
            const next = link_ext orelse break;
            switch (reader.types.payload(next)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .empty_tag_union => break,
                .tag_union => |more| {
                    link_tags = more.tags;
                    link_ext = more.ext;
                },
                .alias => |alias| {
                    link_tags = .empty;
                    link_ext = alias.backing;
                },
                .flex, .rigid => {
                    const fixed = reader.fixedTypeIn(frame, next) orelse {
                        tail = .{ .reader = reader, .id = next, .frame = frame };
                        break;
                    };
                    reader = fixed.reader;
                    frame = fixed.frame;
                    link_tags = .empty;
                    link_ext = fixed.id;
                },
                .nominal, .tuple, .function, .record, .empty_record, .pending, .err => {
                    tail = .{ .reader = reader, .id = next, .frame = frame };
                    break;
                },
            }
        }
        std.mem.sort(VariantRef, variants.items, {}, tagLabelLessThan);
        hasher.update("tag_union");
        for (variants.items) |variant| {
            const label = variant.reader.names.tagLabelText(variant.tag.name);
            hasher.update(std.mem.asBytes(&label.len));
            hasher.update(label);
            const payloads = variant.tag.args;
            hasher.update(std.mem.asBytes(&payloads.len));
            for (payloads) |payload| try hashBinding(hasher, variant.reader.resolvedTypeIn(variant.frame, payload));
        }
        if (tail) |end| try hashBinding(hasher, end) else hasher.update("closed");
        return true;
    }

    /// The concrete type a checked id names here, which for a quantified
    /// variable is what the call being walked fixed it to.
    fn resolvedType(self: *Reifier, type_id: CheckedTypeId) FramedType {
        return self.resolvedTypeIn(self.frame, type_id);
    }

    /// `resolvedType` in `frame`, where a type reference names its variables.
    fn resolvedTypeIn(self: *Reifier, frame: FrameId, type_id: CheckedTypeId) FramedType {
        return self.fixedTypeIn(frame, type_id) orelse .{ .reader = self, .id = type_id, .frame = frame };
    }

    /// What a variable stands for here: what the call fixed a quantified
    /// variable to, or what a use fixed a nominal's declared variable to.
    fn fixedType(self: *Reifier, type_id: CheckedTypeId) ?FramedType {
        return self.fixedTypeIn(self.frame, type_id);
    }

    /// `fixedType` in `frame`.
    fn fixedTypeIn(self: *Reifier, frame: FrameId, type_id: CheckedTypeId) ?FramedType {
        if (self.walk.frameSubstitution(frame).get(type_id)) |fixed| return fixed;
        if (self.nominal_args.get(type_id)) |fixed| return fixed;
        return self.related.get(type_id);
    }

    /// Relate every monomorphic dispatch target that publication selected for
    /// a callable checking never instantiated to that callable, once per
    /// module.
    ///
    /// Such an edge is `derived_from_callable`: publication chose the target
    /// (the procedure an alias reaches, or a literal conversion), and the
    /// edge's contract is that specialization relates the target's type to
    /// the callable. Monotype honours the contract when it lowers the
    /// dispatch, and a description is the same specialization read without
    /// lowering, so the walk honours it here. A dispatcher no edge pins has
    /// no selected target: the walk reaches its default owner's method
    /// (`defaultOwnerMethod`) and relates it the same way. That is what
    /// fixes `y` in `|x, y| x + y`: `x` seals to `Dec`, its owner's `plus`
    /// is `Dec.plus : Dec, Dec -> Dec`, and that fixes the other argument
    /// and the result. A generic target fixes none of the callable's
    /// variables by its own type, so it is not related.
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
                .local_proc, .structural, .callable_binding => continue,
            };
            const target = try self.targetTemplate(procedure.template, try self.methodTargetDef(procedure, node.target) orelse continue) orelse continue;
            if (target.reader.schemeVars(target.template).len != 0) continue;
            const target_fn: FramedType = .{ .reader = target.reader, .id = target.template.checked_fn_root, .frame = empty_frame };
            if (!self.fitsTarget(callable, target_fn)) {
                if (node.dispatcher_ty) |dispatcher| try self.unfit.put(self.gpa, dispatcher, {});
                continue;
            }
            variables.clearRetainingCapacity();
            seen.clearRetainingCapacity();
            try self.collectVariables(&variables, &seen, callable);
            try self.matchType(&self.related, variables.items, callable, target_fn);
        }
        // A dispatcher no edge pins reaches its default owner's method in
        // the walk (`defaultOwnerMethod`), which relates to the dispatch's
        // callable as a selected target does.
        for (self.plans.plans) |plan| {
            const target = self.defaultOwnerMethod(plan.resolution, plan.dispatcher_ty, plan.method) orelse continue;
            const procedure = switch (target.kind) {
                .procedure => |procedure| procedure,
                .local_proc, .structural, .callable_binding => continue,
            };
            const found = try self.targetTemplate(procedure.template, try self.methodTargetDef(procedure, target) orelse continue) orelse continue;
            if (found.reader.schemeVars(found.template).len != 0) continue;
            const target_fn: FramedType = .{ .reader = found.reader, .id = found.template.checked_fn_root, .frame = empty_frame };
            if (!self.fitsTarget(plan.callable_ty, target_fn)) {
                try self.unfit.put(self.gpa, self.throughAliases(plan.dispatcher_ty), {});
                continue;
            }
            variables.clearRetainingCapacity();
            seen.clearRetainingCapacity();
            try self.collectVariables(&variables, &seen, plan.callable_ty);
            try self.matchType(&self.related, variables.items, plan.callable_ty, target_fn);
        }
    }

    /// Whether a monomorphic target's type agrees with a callable everywhere
    /// the callable is not a variable, so relating the two fixes the
    /// callable's variables rather than contradicting its concrete parts.
    fn fitsTarget(self: *Reifier, callable: CheckedTypeId, target: FramedType) bool {
        const use = target.reader.resolvedTypeIn(target.frame, target.id);
        const use_payload = use.reader.types.payload(use.id);
        switch (use_payload) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .alias => |alias| return self.fitsTarget(callable, .{ .reader = use.reader, .id = alias.backing, .frame = use.frame }),
            // The target leaves this part to the callable.
            .flex, .rigid => return true,
            .pending, .err => return false,
            .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => {},
        }
        return switch (self.types.payload(callable)) {
            .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
            .flex, .rigid => true,
            .alias => |alias| self.fitsTarget(alias.backing, use),
            .pending, .err => false,
            .empty_record => use_payload == .empty_record,
            .empty_tag_union => use_payload == .empty_tag_union,
            .function => |fn_ty| blk: {
                const use_fn = switch (use_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .function => |use_fn| use_fn,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .nominal, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (fn_ty.args.len != use_fn.args.len) break :blk false;
                for (fn_ty.args, use_fn.args) |arg, use_arg| {
                    if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg, .frame = use.frame })) break :blk false;
                }
                break :blk self.fitsTarget(fn_ty.ret, .{ .reader = use.reader, .id = use_fn.ret, .frame = use.frame });
            },
            .nominal => |nominal| blk: {
                const use_nominal = switch (use_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .nominal => |use_nominal| use_nominal,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                // Ids are each store's own, so this side's names are looked
                // up in the target's store.
                if (use.reader.names.lookupModuleIdentity(self.names.moduleIdentityBytes(nominal.origin_module)) != use_nominal.origin_module) break :blk false;
                if (use.reader.names.lookupTypeName(self.names.typeNameText(nominal.name)) != use_nominal.name) break :blk false;
                if (nominal.args.len != use_nominal.args.len) break :blk false;
                for (nominal.args, use_nominal.args) |arg, use_arg| {
                    if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg, .frame = use.frame })) break :blk false;
                }
                break :blk true;
            },
            .tuple => |parts| blk: {
                const use_parts = switch (use_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .tuple => |use_parts| use_parts,
                    .pending, .err, .flex, .rigid, .alias, .record, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (parts.len != use_parts.len) break :blk false;
                for (parts, use_parts) |part, use_part| {
                    if (!self.fitsTarget(part, .{ .reader = use.reader, .id = use_part, .frame = use.frame })) break :blk false;
                }
                break :blk true;
            },
            .record => |record| blk: {
                const use_record = switch (use_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .record => |use_record| use_record,
                    .pending, .err, .flex, .rigid, .alias, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => break :blk false,
                };
                if (record.fields.len() != use_record.fields.len()) break :blk false;
                var fields = record.fields.iterator();
                while (fields.next()) |field| {
                    const name = use.reader.names.lookupRecordFieldLabel(self.names.recordFieldLabelText(field.name)) orelse break :blk false;
                    var use_fields = use_record.fields.iterator();
                    const match = while (use_fields.next()) |use_field| {
                        if (use_field.name == name) break use_field;
                    } else break :blk false;
                    if (!self.fitsTarget(field.ty, .{ .reader = use.reader, .id = match.ty, .frame = use.frame })) break :blk false;
                }
                break :blk self.fitsTarget(record.ext, .{ .reader = use.reader, .id = use_record.ext, .frame = use.frame });
            },
            .tag_union => |union_ty| blk: {
                const use_union = switch (use_payload) {
                    .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                    .tag_union => |use_union| use_union,
                    .pending, .err, .flex, .rigid, .alias, .record, .tuple, .nominal, .function, .empty_record, .empty_tag_union => break :blk false,
                };
                if (union_ty.tags.len() != use_union.tags.len()) break :blk false;
                var tags = union_ty.tags.iterator();
                while (tags.next()) |variant| {
                    const name = use.reader.names.lookupTagLabel(self.names.tagLabelText(variant.name)) orelse break :blk false;
                    var use_tags = use_union.tags.iterator();
                    const match = while (use_tags.next()) |use_variant| {
                        if (use_variant.name == name) break use_variant;
                    } else break :blk false;
                    const args = variant.args;
                    const use_args = match.args;
                    if (args.len != use_args.len) break :blk false;
                    for (args, use_args) |arg, use_arg| {
                        if (!self.fitsTarget(arg, .{ .reader = use.reader, .id = use_arg, .frame = use.frame })) break :blk false;
                    }
                }
                break :blk self.fitsTarget(union_ty.ext, .{ .reader = use.reader, .id = use_union.ext, .frame = use.frame });
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
            // A field kind a substitution binds names no variable.
            .field_kind => {},
            .flex, .rigid => try found.append(self.gpa, id),
            .alias => |alias| try self.collectVariables(found, seen, alias.backing),
            .function => |fn_ty| {
                for (fn_ty.args) |arg| try self.collectVariables(found, seen, arg);
                try self.collectVariables(found, seen, fn_ty.ret);
            },
            .nominal => |nominal| for (nominal.args) |arg| try self.collectVariables(found, seen, arg),
            .tuple => |parts| for (parts) |part| try self.collectVariables(found, seen, part),
            .record => |record| {
                var fields = record.fields.iterator();
                while (fields.next()) |field| try self.collectVariables(found, seen, field.ty);
                try self.collectVariables(found, seen, record.ext);
            },
            .tag_union => |union_ty| {
                var tags = union_ty.tags.iterator();
                while (tags.next()) |variant| {
                    for (variant.args) |arg| try self.collectVariables(found, seen, arg);
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
    parameter: struct { reader: *Reifier, pattern: PatternId, position: u32 },
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

fn exprFormName(data: checked_bodies.ExprData) []const u8 {
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
        .structural_eq, .method_eq => "an equality comparison",
        .structural_hash => "a derived hash",
        .run_low_level => "a compiler intrinsic",
        .ellipsis => "...",
        .runtime_error => "an expression that failed to compile",
        .numeral,
        .code_site,
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

fn patternFormName(data: checked_bodies.PatternData) []const u8 {
    return switch (data) {
        .list => "a list pattern",
        .str_interpolation => "a string interpolation pattern",
        .runtime_error => "a pattern that failed to compile",
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

fn statementFormName(data: checked_bodies.StatementData) []const u8 {
    return switch (data) {
        .expr => "a statement expression",
        .dbg => "dbg",
        .expect => "expect",
        .crash => "crash",
        .for_ => "for",
        .return_ => "return",
        .decl,
        .promoted_proc,
        .var_,
        .var_uninitialized,
        .reassign,
        .while_,
        .infinite_loop,
        .breakable_loop,
        .break_,
        .rejected_method_decl,
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
    expr: ExprId,
    /// The site's region in its module, where a refusal in another module's
    /// source is reported from.
    region: base.Region,
    outcome: Outcome,
    /// The site's input slots, in slot order. Empty unless the site's
    /// translator returns a `Code.Bound` and the description reads a value
    /// that exists only at run time.
    slots: []SlotSource = &.{},
    /// The call that binds the site's input slots, as the checker recorded
    /// it, or null.
    bound_call: ?u32 = null,
    /// What stopped the calls that carry the site, as the checker recorded
    /// it, when no call binds its run-time reads.
    chain_stop: CodeSiteRecord.ChainStop = .none,
    /// The expression those calls ended in, as the checker recorded it, when
    /// `chain_stop` is set.
    chain_end: ?ExprId = null,
    /// Why `bound_call` is no compile-time root of its own, as the checker
    /// recorded it, where it is none.
    bound_root: CodeSiteRecord.BoundRoot = .other,
    /// The conversion roots of the custom literals the walk met, which
    /// lowering reads where the site stands. Owned.
    reads: []checked.CheckedCodeRead = &.{},
};

/// What the program supplies for one input slot: a run-time name, read
/// through these projections at the call (N18b), or the value of a value
/// site (R12), with no projection.
pub const SlotSource = struct {
    source: checked.CheckedCodeSlot.Source,
    steps: []const SlotStep,
    /// The slot type's shape (`slotShape`), which the site lowering checks
    /// the value it builds against in debug builds. An encoded slot's shape
    /// is the one word `encoded`.
    shape: []const u32,
    /// The encoder of a slot whose type holds an opaque type: the expression
    /// `T.encoder_for(fmt.default())` of the capture read the slot is.
    encoder: ?ExprId = null,
};

/// What one numbered input leaf of a walk is: a run-time name the
/// description reads, or the value of a value site (R12).
pub const InputLeaf = union(enum) {
    binder: BinderId,
    value: ExprId,
};

/// One capture read of a lambda at a `Code.Binds` position, as a slot path:
/// the captured name and the projections the read applies, with the
/// encoder the checker required for the read (rule "Bound Capture
/// Encoding").
pub const CaptureRead = struct {
    leaf: BinderId,
    steps: []const SlotStep,
    encoder: ExprId,
};

/// The capture reads of the lambda `site`, as slot paths, read from CIR and
/// the reads the checker recorded for the site
/// (`ModuleEnv.bound_capture_encodings`). Owned.
fn captureReads(gpa: Allocator, reifier: *Reifier, site: ExprId) Allocator.Error![]CaptureRead {
    const bodies = reifier.bodies;
    const bound = reifier.env.boundCaptureEncodingsForSite(@backingInt(site));
    const out = try gpa.alloc(CaptureRead, bound.len);
    var made: usize = 0;
    errdefer {
        for (out[0..made]) |read| gpa.free(read.steps);
        gpa.free(out);
    }
    var steps = std.ArrayList(SlotStep).empty;
    defer steps.deinit(gpa);
    for (bound) |entry| {
        steps.clearRetainingCapacity();
        const read: ExprId = @fromBackingInt(entry.read_expr);
        var current = read;
        const leaf: ?BinderId = while (true) {
            switch (bodies.expr(current).data) {
                .lookup_local => |pattern| break reifier.binderOf(pattern) orelse
                    invariant("a capture read names a pattern with no binder"),
                .field_access => |access| {
                    var i = access.segments.len;
                    while (i > 0) {
                        i -= 1;
                        try steps.append(gpa, .{ .field = bodies.fieldAccessSegment(access.segments, @intCast(i)).field_name });
                    }
                    current = access.receiver;
                },
                .tuple_access => |access| {
                    try steps.append(gpa, .{ .index = access.elem_index });
                    current = access.tuple;
                },
                // A capture read that failed to check is an error, and the
                // site is left to it.
                .numeral,
                .code_site,
                .str_segment,
                .str,
                .bytes_literal,
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
                .dispatch_call,
                .interpolation,
                .structural_eq,
                .structural_hash,
                .method_eq,
                .type_dispatch_call,
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
                => break null,
            }
        };
        if (leaf == null) continue;
        std.mem.reverse(SlotStep, steps.items);
        // The read itself is its encoder: lowering builds the encoder call
        // from the read's plan (`boundCaptureEncoderPlan`).
        out[made] = .{ .leaf = leaf.?, .steps = try gpa.dupe(SlotStep, steps.items), .encoder = read };
        made += 1;
    }
    return gpa.realloc(out, made);
}

fn freeCaptureReads(gpa: Allocator, reads: []CaptureRead) void {
    for (reads) |read| gpa.free(read.steps);
    gpa.free(reads);
}

/// The published form of one slot step.
fn slotStepRecord(step: SlotStep) checked.CheckedCodeSlotStep {
    return switch (step) {
        .field => |label| .{ .kind = .field, .value = @backingInt(label) },
        .index => |index| .{ .kind = .index, .value = index },
        .unwrap => .{ .kind = .unwrap, .value = 0 },
    };
}

/// Whether a slot type holds an opaque type anywhere, so that the program
/// binds it as the bytes of its encoder (`Code.Value.Encoded`). The checker
/// asks the same question of a capture read (`code_opacity.holds`).
fn holdsOpaque(gpa: Allocator, types: *const Types, ty: TyId) Allocator.Error!bool {
    const reader = struct {
        types: *const Types,
        gpa: Allocator,
        pub fn read(self: @This(), current: TyId, pending: *std.ArrayList(TyId)) Allocator.Error!code_opacity.Node {
            switch (self.types.get(current)) {
                .opaque_ => return .opaque_,
                .func, .int, .float, .dec, .bool_, .str, .recursive => {},
                .list => |elem| try pending.append(self.gpa, elem),
                .nominal => |n| try pending.append(self.gpa, n.backing),
                .tuple => |span| try pending.appendSlice(self.gpa, self.types.tySlice(span)),
                .record => |span| for (self.types.memberSlice(span)) |field| try pending.appendSlice(self.gpa, self.types.tySlice(field.tys)),
                .tag_union => |span| for (self.types.memberSlice(span)) |tag| try pending.appendSlice(self.gpa, self.types.tySlice(tag.tys)),
            }
            return .inner;
        }
    }{ .types = types, .gpa = gpa };
    return try code_opacity.holds(TyId, gpa, reader, ty) == .opaque_;
}

/// One projection of a slot source.
pub const SlotStep = union(enum) {
    field: canonical.RecordFieldLabelId,
    index: u32,
    unwrap,
};

fn sameSteps(a: []const SlotStep, b: []const SlotStep) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| {
        const same = switch (x) {
            .field => |label| y == .field and y.field == label,
            .index => |k| y == .index and y.index == k,
            .unwrap => y == .unwrap,
        };
        if (!same) return false;
    }
    return true;
}

/// Why a slot whose type holds an opaque type has no encoder: the site is no
/// `Code.Binds` position, or the slot is a value the description reads other
/// than as a capture read (`{ at } = order`, then `at`).
fn opaqueSlotRefusal(binds: bool, steps: []const SlotStep) []const u8 {
    if (!binds) return "a captured value of an opaque type, which a translator binds only through a `Code.Binds` parameter that names its format";
    for (steps) |step| switch (step) {
        .unwrap => return "a value of an opaque type inside a captured nominal value; read the captured value itself",
        .field, .index => {},
    };
    return "a value of an opaque type that the function does not read as a captured name or a field of one; read it as the field path itself, such as `order.at` instead of `{ at } = order` and `at`";
}

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
            .int => |int| try out.appendSlice(gpa, &.{ @backingInt(S.int), @backingInt(int) }),
            .float => |float| try out.appendSlice(gpa, &.{ @backingInt(S.frac), @intFromBool(float == .f64) }),
            .dec => try out.append(gpa, @backingInt(S.dec)),
            .bool_ => try out.append(gpa, @backingInt(S.bool_)),
            .str => try out.append(gpa, @backingInt(S.str)),
            .recursive => try out.append(gpa, @backingInt(S.recursive)),
            .list => |elem| {
                try out.append(gpa, @backingInt(S.list));
                try pending.append(gpa, .{ .ty = elem });
            },
            .nominal => |n| {
                try out.append(gpa, @backingInt(S.wrap));
                try pending.append(gpa, .{ .ty = n.backing });
            },
            .tuple => |span| {
                const items = types.tySlice(span);
                try out.appendSlice(gpa, &.{ @backingInt(S.tuple), @intCast(items.len) });
                var i = items.len;
                while (i > 0) {
                    i -= 1;
                    try pending.append(gpa, .{ .ty = items[i] });
                }
            },
            .record => |span| {
                const fields = types.memberSlice(span);
                try out.appendSlice(gpa, &.{ @backingInt(S.record), @intCast(fields.len) });
                var i = fields.len;
                while (i > 0) {
                    i -= 1;
                    const field = fields[i];
                    const label = names.lookupRecordFieldLabel(types.nameText(field.name)) orelse
                        invariant("a field of a slot type has no label in the site's module");
                    try pending.append(gpa, .{ .ty = types.tySlice(field.tys)[0] });
                    // An optional field's value may be absent (`Code.Value.Absent`).
                    if (field.optional) try pending.append(gpa, .{ .word = @backingInt(S.opt_field) });
                    try pending.append(gpa, .{ .word = @backingInt(label) });
                }
            },
            .tag_union => |span| {
                const tags = types.memberSlice(span);
                try out.appendSlice(gpa, &.{ @backingInt(S.tag_union), @intCast(tags.len) });
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
) ?ExprId {
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
    body: ExprId,
};

/// One module the walk reads: its finished checked data, and its own view
/// of the modules in its reach, which its code slots read the imported
/// modules' slots through. The slot of a module's cuts takes it as
/// `CutInputs`, the slot of its inventories as `PlanInputs`.
pub const ModuleInputs = struct {
    sources: Reifier.Sources,
    lookup: ForeignLookup,

    pub fn env(self: ModuleInputs) *const ModuleEnv {
        return self.sources.bodies.env;
    }
};

/// Another module the walk reads.
pub const ForeignModule = ModuleInputs;

/// The inputs of a module's `codeCuts` slot (`moduleCuts`).
pub const CutInputs = ModuleInputs;

/// The inputs of a module's `codeInventories` slot (`planModule`).
pub const PlanInputs = ModuleInputs;

/// An exact function alias another module exports, `same = add_one`: the
/// module that holds it, and the lookup the checker recorded as the function
/// the alias names.
pub const ForeignAlias = struct {
    module: ForeignModule,
    lookup: ExprId,
    /// The alias's binding in that module, whose entry wrapper owns the
    /// scope the alias's quantified variables belong to.
    template: checked.CallableEvalTemplateId,
};

/// A top-level value another module exports that computes a function: the
/// module that holds it, the checked expression it was written as, and its
/// callable-eval template in that module.
pub const ForeignComputed = struct {
    module: ForeignModule,
    body: ExprId,
    template: checked.CallableEvalTemplateId,
};

/// A definition another module exports, resolved to what the walk reads.
pub const ForeignDefinition = struct {
    module: ForeignModule,
    /// The checked expression the definition's body is.
    body: ExprId,
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
    /// Whether the module of content identity `module` is the builtin
    /// module, by its role (Q10). A nominal names its declaring module only
    /// by identity, and the builtin module declares nominals the checker
    /// marks as no builtin (`Hasher`), so the walk asks rather than reads
    /// the name.
    resolve_builtin_module: *const fn (
        context: *const anyopaque,
        module: *const [32]u8,
    ) bool,
    /// The definition a lookup of the module being walked names, as checking
    /// resolved it: the module that declares it and the definition. Null for
    /// a lookup of a local name or of no definition.
    resolve_lookup_target: *const fn (
        context: *const anyopaque,
        expr_idx: CIR.Expr.Idx,
    ) ?checked.LookupTarget,
    /// A module in reach by its key: the module a recipe's root lives in
    /// (D1), which may be one the module of a closing use never imported.
    resolve_module: *const fn (
        context: *const anyopaque,
        key: *const [32]u8,
    ) ?ForeignModule,
    /// A module in reach by its content identity, as a field default names
    /// its declaring module (D5).
    resolve_identity_module: *const fn (
        context: *const anyopaque,
        identity: *const [32]u8,
    ) ?ForeignModule,
    /// The module an import of this module resolved to, or null for an
    /// import checking left unresolved.
    resolve_import_module: *const fn (
        context: *const anyopaque,
        import_idx: CIR.Import.Idx,
    ) ?ForeignModule,

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
        .resolve_builtin_module = resolveNothingBuiltinModule,
        .resolve_lookup_target = resolveNothingLookupTarget,
        .resolve_module = resolveNothingModule,
        .resolve_identity_module = resolveNothingModule,
        .resolve_import_module = resolveNothingImportModule,
    };

    fn resolveNothingImportModule(_: *const anyopaque, _: CIR.Import.Idx) ?ForeignModule {
        return null;
    }

    fn resolveNothingModule(_: *const anyopaque, _: *const [32]u8) ?ForeignModule {
        return null;
    }

    fn resolveNothingLookupTarget(_: *const anyopaque, _: CIR.Expr.Idx) ?checked.LookupTarget {
        return null;
    }

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

    fn resolveNothingBuiltinModule(_: *const anyopaque, _: *const [32]u8) bool {
        return false;
    }

    /// Whether `module` is the content identity of the builtin module.
    fn isBuiltinModule(self: ForeignLookup, module: *const [32]u8) bool {
        return self.resolve_builtin_module(self.context, module);
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

    fn findModule(self: ForeignLookup, key: *const [32]u8) ?ForeignModule {
        return self.resolve_module(self.context, key);
    }

    fn findImportModule(self: ForeignLookup, import_idx: CIR.Import.Idx) ?ForeignModule {
        return self.resolve_import_module(self.context, import_idx);
    }

    fn findModuleByIdentity(self: ForeignLookup, identity: *const [32]u8) ?ForeignModule {
        return self.resolve_identity_module(self.context, identity);
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
    store: ?*ConstStore,
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
    closure_targets: collections.DenseMapUnmanaged(RowId, Reifier.CalleeTarget) = .empty,
    /// The root row of the site last emitted, which a test dumps.
    root: ?RowId = null,
    rejection: ?Rejection = null,
    /// The reader whose module's source the walk is reading: the site's, or
    /// that of the callee or constant it entered (`Reifier.enter`). A refusal
    /// is placed in this module, because its region indexes this source.
    body: ?*Reifier = null,
    /// The part of a row's signature whose type `tyOf` is building, which a
    /// refusal at a type variable names. `.expression` everywhere else.
    place: TypePlace = .expression,
    /// The quantified variable whose substitution `tyOf` is inside, the
    /// outermost one, or null outside every substitution. A variable the
    /// use left open is named by the one the annotation wrote.
    through: ?Reifier.FramedType = null,
    /// The nominals `tyOf` is part way through building, outermost first,
    /// in every reader: a `Recursive` refers to the nearest one of its name,
    /// whichever module's reader opened it.
    open_nominals: std.ArrayList(OpenNominal) = .empty,
    /// The frames of the site being walked: frame `n` is `frames[n - 1]`,
    /// the substitution of one instance the walk entered, and frame 0
    /// (`Reifier.empty_frame`) is the empty one. A type reference names its
    /// frame, so a binding is read in the frame it was made in (D2). Freed
    /// when the next site starts.
    frames: std.ArrayList(Reifier.Substitution) = .empty,
    /// The view the site being walked declares (plan 1.5, V6).
    view: View = .graph,
    /// The name of the outermost top-level constant the walk is folding, or
    /// null outside every one. A refusal of a `Code` value names it (D7).
    constant: ?[]const u8 = null,
    /// The site's cut (I14, N8h): each function the `code_primitives` item of
    /// its translator's type lists, by what a callee resolves to, with the
    /// name its `Prim` carries. Every other function is walked (N8l).
    cut: std.AutoHashMapUnmanaged(Reifier.CutKey, Reifier.ForeignName) = .empty,
    /// Where set, the walk measures K (`ROC_REIFY_OUTLINE_STATS`): `finish`
    /// prints the size of the site's `outline` view at this K and emits
    /// nothing.
    measure_k: ?u32 = null,
    /// The index of the site's first input slot among the slots of the call
    /// that binds it: the slots of the call's earlier sites, in site order.
    /// Zero for a site no call binds.
    first_slot: u64 = 0,
    /// The site begun last is a value site no call binds (R12): its normal
    /// form must be a data literal, or the site is refused.
    value_literal: bool = false,
    /// The walk reads an opaque type of a package as its backing, and the
    /// operations of such a type as functions it walks, not as primitives
    /// (`readsOpaque`). Only a value site no call binds sets it, after it
    /// checked that its own type holds no opaque type (`valueRow`): the site
    /// computes a data literal, and that literal shows no opaque type.
    opaque_backings: bool = false,
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
    /// The conversion roots of the custom literals the site's walk met, in
    /// the order it met them, once each. `takeReads` hands them over.
    reads: std.ArrayList(checked.CheckedCodeRead) = .empty,
    /// The key of the instance of the template that holds the site being
    /// walked, for an instance site (D1), or null. A site key mixes it in,
    /// so each instance's description has a key of its own.
    instance: ?[32]u8 = null,

    /// The run-time names a site that binds inputs reads.
    pub const Inputs = struct {
        /// The reader of the site's own module, the only module whose
        /// run-time names the call can supply.
        reader: *Reifier,
        /// Each leaf the walk numbered, by its number (`ir.Slot.Source.leaf`).
        leaves: std.ArrayList(InputLeaf) = .empty,
        /// The capture reads of a lambda at a `Code.Binds` position, with the
        /// encoder the checker required for each (`captureReads`). Owned.
        captures: []CaptureRead = &.{},
        /// For a site of a generic bound call, the call's leaves
        /// (`checked.appendBoundSiteLeaves`): every name the walk makes a
        /// slot of is one of them.
        call_leaves: ?[]const BinderId = null,
    };

    /// One nominal `tyOf` is building: the name its `Recursive` carries, in
    /// the name store of the reader of its module, and its declaration with
    /// what this use fixed its variables to.
    const OpenNominal = struct {
        reader: *Reifier,
        name: canonical.TypeNameId,
        instance: Reifier.NominalInstanceKey,
    };

    /// A normal form P1 keeps: its `Graph`, its nodes' origins, and the
    /// slots its root reads, in slot order.
    const Normalized = struct {
        graph: ConstNodeId,
        /// The digests of the nodes of an `inline` view (V5a); null for `graph`.
        digests: ?ConstNodeId,
        origins: reify.provenance.Emitted,
        slot_order: []ir.SlotId,
        /// The root row delivers a data literal (`rootDeliversDataLiteral`).
        data_literal: bool,
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

    /// `store` is null for a walk that writes no description: the walks
    /// of the `codeCuts` and `codeInventories` slots.
    pub fn init(gpa: Allocator, store: ?*ConstStore, foreign: ForeignLookup) Walk {
        return .{ .gpa = gpa, .store = store, .foreign = foreign };
    }

    /// The store a description is written into. Only the description step
    /// writes one.
    fn constStore(self: *Walk) *ConstStore {
        return self.store orelse invariant("a walk of a code slot wrote a description");
    }

    pub fn deinit(self: *Walk) void {
        for (self.readers.items) |open| {
            open.deinit();
            self.gpa.destroy(open);
        }
        self.readers.deinit(self.gpa);
        self.endSite();
        self.cut.deinit(self.gpa);
        self.definitions.deinit(self.gpa);
        self.rows.deinit(self.gpa);
        self.open_nominals.deinit(self.gpa);
        self.clearClosureTargets();
        self.closure_targets.deinit(self.gpa);
        self.clearFrames();
        self.frames.deinit(self.gpa);
        var memo = self.normalized.valueIterator();
        while (memo.next()) |m| {
            m.origins.deinit(self.gpa);
            self.gpa.free(m.slot_order);
        }
        self.normalized.deinit(self.gpa);
        self.endInputs();
        self.freeSlots();
        self.reads.deinit(self.gpa);
        self.sources.deinit(self.gpa);
        self.source_ids.deinit(self.gpa);
        for (self.published.items) |*p| p.deinit(self.gpa);
        self.published.deinit(self.gpa);
    }

    /// The module whose source the walk is reading, where a refusal is
    /// placed. Every walk reads some module's source before it can refuse.
    fn bodyModule(self: *const Walk) Rejection.Module {
        const body = self.body orelse invariant("a refusal before the walk read any module's source");
        return body.rejectionModule();
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
        opened.* = Reifier.init(self, module);
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
        self.cut.clearRetainingCapacity();
        self.rejection = null;
        self.constant = null;
        self.endInputs();
        self.freeSlots();
        self.reads.clearRetainingCapacity();
        self.body = site_reader;
        self.first_slot = 0;
        self.value_literal = false;
        if (binds_inputs) self.inputs = .{ .reader = site_reader };
    }

    /// Take the cut of the site begun last from its translator (I14): the
    /// function that `call`, a call `site_reader` checked, names. The
    /// nominal type that has that function as an associated item declares
    /// the cut with its `code_primitives` item, which publication of the
    /// type's module checked. A translator that is no such function, or whose
    /// type declares no cut, leaves the cut empty.
    pub fn useCut(self: *Walk, site_reader: *Reifier, call: ExprId) Allocator.Error!void {
        const function = try site_reader.translatorFunction(call) orelse return;
        const owner = function.reader;
        const owned = owner.ownerOf(function.def) orelse return;
        const members = (try owner.codeCuts()).membersOf(owned.decl) orelse return;
        for (members) |lookup| {
            const member_resolved = owner.lookupResolved(lookup) orelse
                invariant("a cut member is a lookup, which publication checked");
            const member = try owner.listedMember(member_resolved) orelse
                invariant("a cut member names a function or a constant, which publication checked");
            try self.cut.put(self.gpa, .{ .artifact = member.reader.artifact.bytes, .body = member.body }, member.reader.qualifiedName(member.def));
        }
    }

    /// Note that the walk met a literal whose conversion is a compile-time
    /// root of `module`, so lowering reads that root where the site stands.
    fn noteRead(self: *Walk, module: checked.CheckedModuleArtifactKey, root: checked.ComptimeRootId) Allocator.Error!void {
        for (self.reads.items) |read| {
            if (read.root == @backingInt(root) and module.eql(.{ .bytes = read.module })) return;
        }
        try self.reads.append(self.gpa, .{ .module = module.bytes, .root = @backingInt(root) });
    }

    /// The roots of the site last finished, which the caller now owns.
    pub fn takeReads(self: *Walk) Allocator.Error![]checked.CheckedCodeRead {
        return self.reads.toOwnedSlice(self.gpa);
    }

    fn endInputs(self: *Walk) void {
        if (self.inputs) |*inputs| {
            inputs.leaves.deinit(self.gpa);
            freeCaptureReads(self.gpa, inputs.captures);
        }
        self.inputs = null;
    }

    /// Give the site begun last the capture reads of its lambda at a
    /// `Code.Binds` position, which bind a slot whose type holds an opaque
    /// type. Takes `captures`.
    pub fn useCaptureReads(self: *Walk, captures: []CaptureRead) void {
        const inputs = &(self.inputs orelse {
            freeCaptureReads(self.gpa, captures);
            return;
        });
        freeCaptureReads(self.gpa, inputs.captures);
        inputs.captures = captures;
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

    /// A frame holding a copy of `substitution`, which the caller keeps.
    fn pushFrame(self: *Walk, substitution: Reifier.Substitution) Allocator.Error!Reifier.FrameId {
        var copy = try substitution.clone(self.gpa);
        errdefer copy.deinit(self.gpa);
        try self.frames.append(self.gpa, copy);
        return @intCast(self.frames.items.len);
    }

    /// The substitution frame `frame` holds.
    fn frameSubstitution(self: *const Walk, frame: Reifier.FrameId) *const Reifier.Substitution {
        if (frame == Reifier.empty_frame) return &empty_substitution;
        return &self.frames.items[frame - 1];
    }

    const empty_substitution: Reifier.Substitution = .empty;

    fn clearFrames(self: *Walk) void {
        for (self.frames.items) |*frame| frame.deinit(self.gpa);
        self.frames.clearRetainingCapacity();
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
        self.clearFrames();
        self.stage_one = 0;
        self.open_builtins = false;
        self.sources.clearRetainingCapacity();
        self.source_ids.clearRetainingCapacity();
        self.root = null;
        self.rejection = null;
        self.opaque_backings = false;
        self.clearTyCaches();
        self.open_nominals.clearRetainingCapacity();
    }

    /// Forget each type the readers built: a type built is in the site's
    /// store, and how it reads an opaque type follows `opaque_backings`.
    fn clearTyCaches(self: *Walk) void {
        for (self.readers.items) |open| {
            open.ty_cache.clearRetainingCapacity();
            open.type_in_progress.clearRetainingCapacity();
        }
    }

    /// Read each opaque type of a package as its backing from here on in
    /// this site (`opaque_backings`).
    fn readOpaqueBackings(self: *Walk) void {
        std.debug.assert(self.value_literal and !self.opaque_backings);
        self.opaque_backings = true;
        self.clearTyCaches();
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
        _ = try self.normalizeWith(root, region, viewOf(self.view), .{ .laws = self.view == .lawful });
    }

    fn viewOf(view: View) reify.driver.View {
        return switch (view) {
            .graph, .lawful => .graph,
            .inline_ => .inline_,
            .outline => .outline,
        };
    }

    fn normalizeWith(self: *Walk, root: RowId, region: base.Region, view: reify.driver.View, options: reify.driver.Options) error{ Rejected, OutOfMemory }!reify.driver.Stats {
        const site = self.site.?;
        return reify.driver.runToWith(self.gpa, &site.builder, root, &.{}, view, options) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.RoundBoundExceeded => {
                self.rejection = .{ .kind = .bound_exceeded, .region = region, .module = self.bodyModule(), .detail = "simplify rounds per component" };
                return error.Rejected;
            },
            error.UnresolvedApply => {
                self.rejection = .{ .kind = .unsupported_expression, .region = region, .module = self.bodyModule(), .detail = "a call to a function value that no simplification resolves" };
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
        // `measure_k` is set only under `reify_outline_stats`; without developer diagnostics the
        // branch is dead, so a build without an `Io` (wasm) does not analyze `std.debug.print`.
        const measure_k = if (base.dev_diagnostics.available) self.measure_k else null;
        if (measure_k) |k| {
            const stats = try self.normalizeWith(root, region, .outline, .{ .outline_min_size = k });
            std.debug.print("reify outline: site {d}..{d} K={d}: inline {d} nodes and {d} call arguments in {d} rows, outline {d} nodes and {d} call arguments in {d} rows, {d} rows made in {d} passes\n", .{
                region.start.offset,      region.end.offset,       k,
                stats.inline_size.nodes,  stats.inline_size.args,  stats.inline_size.rows,
                stats.outline_size.nodes, stats.outline_size.args, stats.outline_size.rows,
                stats.outline_rows,       stats.outline_passes,
            });
            self.rejection = .{ .kind = .bound_exceeded, .region = region, .module = self.bodyModule(), .detail = "measured, not emitted" };
            return error.Rejected;
        }
        const walked = try reify.rows.walkedDigest(self.gpa, &site.store, &site.types, root);
        const memo_key = .{ self.view, walked ^ slotsDigest(&site.store), reify.provenance.digest(&site.store) };
        if (self.normalized.get(memo_key)) |memo| {
            if (self.value_literal and !memo.data_literal) return self.refuseValueLiteral(region);
            try self.bindSlots(memo.slot_order, region);
            try self.publish(site_key, &memo.origins);
            var emitter = try code_emit.Emitter.init(self.gpa, self.constStore(), &site.store, &site.types);
            defer emitter.deinit();
            if (memo.digests) |digests| return emitter.inlinedOf(memo.graph, digests, self.first_slot, site_key);
            return emitter.siteOf(memo.graph, self.first_slot, site_key);
        }
        try self.normalize(root, region);
        self.normalizations += 1;
        const data_literal = try rootDeliversDataLiteral(self.gpa, &site.store, root);
        if (self.value_literal and !data_literal) return self.refuseValueLiteral(region);
        // Normalizing adds nodes, which the emitter indexes.
        var emitter = try code_emit.Emitter.init(self.gpa, self.constStore(), &site.store, &site.types);
        defer emitter.deinit();
        self.root = root;
        const graph = try emitter.graph(root);
        const digests: ?ConstNodeId = switch (self.view) {
            .graph, .outline, .lawful => null,
            .inline_ => try emitter.digests(root),
        };
        try self.bindSlots(emitter.slot_order, region);
        var origins = try reify.provenance.emitted(self.gpa, &site.store, root);
        errdefer origins.deinit(self.gpa);
        const slot_order = try self.gpa.dupe(ir.SlotId, emitter.slot_order);
        errdefer self.gpa.free(slot_order);
        try self.publish(site_key, &origins);
        try self.normalized.put(self.gpa, memo_key, .{ .graph = graph, .digests = digests, .origins = origins, .slot_order = slot_order, .data_literal = data_literal });
        if (digests) |d| return emitter.inlinedOf(graph, d, self.first_slot, site_key);
        return emitter.siteOf(graph, self.first_slot, site_key);
    }

    /// Refuse a value site no call binds whose normal form is no data
    /// literal: the compiler cannot compute it (R12).
    fn refuseValueLiteral(self: *Walk, region: base.Region) error{ Rejected, OutOfMemory } {
        self.rejection = .{ .kind = .value_not_computable, .region = region, .module = self.bodyModule(), .detail = "" };
        return error.Rejected;
    }

    /// The `Code.Ty` value of `ty`, a type of the site being walked,
    /// written into this module's store (D6).
    pub fn emitTy(self: *Walk, ty: TyId) Allocator.Error!ConstNodeId {
        const site = self.site.?;
        var emitter = try code_emit.Emitter.init(self.gpa, self.constStore(), &site.store, &site.types);
        defer emitter.deinit();
        return emitter.tyValue(ty);
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
            const input_leaf = inputs.leaves.items[leaf];
            shape.clearRetainingCapacity();
            const slot_ty = site.store.slots.items[slot.index()].ty;
            // A slot whose type holds an opaque type is bound as the bytes of
            // its encoder, which the checker required of a capture read only.
            const encoder: ?ExprId = if (try holdsOpaque(self.gpa, &site.types, slot_ty)) blk: {
                const binder = switch (input_leaf) {
                    .binder => |binder| binder,
                    // The whole value is the site's one capture read, at a
                    // `Code.Binds` position. At a plain `Code` the program
                    // has no way to send an opaque value (10.1).
                    .value => |value_site| {
                        if (inputs.reader.env.boundCaptureEncodingsForSite(@backingInt(value_site)).len == 0) {
                            self.rejection = .{ .kind = .value_not_bound, .region = region, .module = self.bodyModule(), .detail = "a value whose type holds an opaque type, at a `Code` position that names no format (`Code.Binds`) to encode it" };
                            return error.Rejected;
                        }
                        try shape.append(self.gpa, @backingInt(checked.CodeValueShape.encoded));
                        break :blk value_site;
                    },
                };
                const read = for (inputs.captures) |capture| {
                    if (capture.leaf == binder and sameSteps(capture.steps, steps.items)) break capture;
                } else {
                    self.rejection = .{ .kind = .input_not_bound, .region = region, .module = self.bodyModule(), .detail = opaqueSlotRefusal(inputs.captures.len != 0, steps.items) };
                    return error.Rejected;
                };
                try shape.append(self.gpa, @backingInt(checked.CodeValueShape.encoded));
                break :blk read.encoder;
            } else blk: {
                if (try slotShape(self.gpa, &site.types, inputs.reader.names, slot_ty, &shape)) |why| {
                    self.rejection = .{ .kind = .input_not_bound, .region = region, .module = self.bodyModule(), .detail = why };
                    return error.Rejected;
                }
                break :blk null;
            };
            const owned_steps = try self.gpa.dupe(SlotStep, steps.items);
            errdefer self.gpa.free(owned_steps);
            dest.* = .{
                .source = switch (input_leaf) {
                    .binder => |binder| .ofBinder(binder),
                    .value => |value_site| .ofValueSite(value_site),
                },
                .steps = owned_steps,
                .shape = try self.gpa.dupe(u32, shape.items),
                .encoder = encoder,
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

/// The argument of each `Code.prim` call the checker accepted in this module,
/// by the call: the reference the call names, which checking did not
/// instantiate (D7, F7).
fn primReferences(gpa: Allocator, env: *const ModuleEnv) Allocator.Error!collections.DenseMapUnmanaged(ExprId, ExprId) {
    var references: collections.DenseMapUnmanaged(ExprId, ExprId) = .empty;
    errdefer references.deinit(gpa);
    for (env.store.codeIdentityUses()) |use| {
        if (use.kind != .prim) continue;
        try references.put(gpa, @fromBackingInt(use.call), @fromBackingInt(use.arg));
    }
    return references;
}

/// Check each `code_primitives` item of a nominal type this module declares,
/// and record the cut it declares (I14, roc-reify-normal-form.md 3.8 and
/// section 12). The item is a `List(Code.PrimId)` (D3): a list of
/// `Code.prim(f)` entries, or the name of a constant of this module that is
/// one, so one list can serve several types. Each entry names a top-level
/// function or constant; an entry that is anything else, that names a
/// definition an earlier entry names, or that names a primitive (a builtin,
/// or an operation of an opaque type, D3) is refused at the entry. The walk
/// reads the references the checker recorded on each `Code.prim` call, not
/// an evaluated value, so an entry with a `where` needs no instance (F7).
///
/// The module's `codeCuts` slot computes this. It writes no description:
/// a refused entry is a problem the description step reports.
pub fn moduleCuts(gpa: Allocator, inputs: CutInputs) Allocator.Error!*code_analyses.CodeCuts {
    const env = inputs.env();
    var cuts = std.ArrayList(code_analyses.CodeCutTable.Cut).empty;
    defer cuts.deinit(gpa);
    var members = std.ArrayList(ExprId).empty;
    defer members.deinit(gpa);
    var problems = std.ArrayList(code_analyses.CutProblem).empty;
    defer problems.deinit(gpa);
    var keys = std.ArrayList(Reifier.CutKey).empty;
    defer keys.deinit(gpa);
    var followed = std.ArrayList(ExprId).empty;
    defer followed.deinit(gpa);

    var walk = Walk.init(gpa, null, inputs.lookup);
    defer walk.deinit();
    var reifier: ?*Reifier = null;
    var references = try primReferences(gpa, env);
    defer references.deinit(gpa);

    for (env.method_defs.entries.items) |entry| {
        if (!entry.key.methodIdent().eql(env.idents.code_primitives)) continue;
        if (env.store.getStatement(entry.key.owner) != .s_nominal_decl) continue;
        const reader = reifier orelse try walk.reader(inputs);
        reifier = reader;
        const written: ExprId = env.store.getDef(entry.value.def_idx).expr;
        // A name of a constant of this module stands for the list that
        // constant was written as.
        followed.clearRetainingCapacity();
        var item = written;
        while (true) {
            try followed.append(gpa, item);
            const constant = try reader.constantDefinition(reader.lookupResolved(item)) orelse break;
            if (constant.reader != reader) break;
            for (followed.items) |seen| {
                if (seen == constant.body) invariant("a constant whose value is its own name is a checked error");
            }
            item = constant.body;
        }
        const listed: []const ExprId = switch (reader.bodies.expr(item).data) {
            .list => |elems| elems,
            .empty_list => &.{},
            // Checking rejected the item, and reported it.
            .runtime_error => continue,
            .numeral,
            .code_site,
            .str_segment,
            .str,
            .bytes_literal,
            .lookup_local,
            .lookup_external,
            .lookup_required,
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
            .field_access,
            .dispatch_call,
            .interpolation,
            .structural_eq,
            .structural_hash,
            .method_eq,
            .type_dispatch_call,
            .tuple_access,
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
            => {
                try problems.append(gpa, .{ .region = reader.bodies.expr(written).source_region, .kind = .not_a_list });
                continue;
            },
        };
        keys.clearRetainingCapacity();
        const start: u32 = @intCast(members.items.len);
        for (listed) |member| {
            const data = reader.bodies.expr(member);
            // Checking reported an entry it rejected.
            if (data.data == .runtime_error) continue;
            const reference = references.get(member);
            const resolved = if (reference) |arg| reader.lookupResolved(arg) else null;
            // An intrinsic is a primitive at every site already.
            if (resolved) |id| if (try reader.listedIntrinsic(id) != null) {
                try problems.append(gpa, .{ .region = data.source_region, .kind = .already_primitive });
                continue;
            };
            const resolved_member = if (resolved) |id| try reader.listedMember(id) else null;
            const named = resolved_member orelse {
                try problems.append(gpa, .{ .region = data.source_region, .kind = .not_a_function });
                continue;
            };
            // The builtin module and the module of an opaque type declare
            // their own primitives, which every description names already.
            if (named.reader.env.module_role == .builtin or try named.reader.primitiveOf(named.def, named.ty) != null) {
                try problems.append(gpa, .{ .region = data.source_region, .kind = .already_primitive });
                continue;
            }
            const key: Reifier.CutKey = .{ .artifact = named.reader.artifact.bytes, .body = named.body };
            const repeated = for (keys.items) |seen| {
                if (std.meta.eql(seen, key)) break true;
            } else false;
            if (repeated) {
                try problems.append(gpa, .{ .region = data.source_region, .kind = .listed_twice });
                continue;
            }
            try keys.append(gpa, key);
            try members.append(gpa, reference.?);
        }
        try cuts.append(gpa, .{
            .owner_decl = entry.key.owner,
            .members = .{ .start = start, .len = @as(u32, @intCast(members.items.len)) - start },
        });
    }

    const result = try gpa.create(code_analyses.CodeCuts);
    errdefer gpa.destroy(result);
    const owned_cuts = try cuts.toOwnedSlice(gpa);
    errdefer gpa.free(owned_cuts);
    const owned_members = try members.toOwnedSlice(gpa);
    errdefer gpa.free(owned_members);
    result.* = .{
        .table = .{ .cuts = owned_cuts, .members = owned_members },
        .problems = try problems.toOwnedSlice(gpa),
    };
    return result;
}

/// The constant one `Code.prim`, `Code.type_id` or `Code.ty_of` call is
/// (D6), or why the call has none.
pub const IdentityOutcome = struct {
    /// The call, which publication replaces with `node`.
    call: ExprId,
    /// The argument, where a refusal is reported.
    region: base.Region,
    outcome: union(enum) {
        node: ConstNodeId,
        /// `Code.prim` of a reference that names no function or constant a
        /// description can name: a function the host provides, a builtin
        /// the compiler writes, a top-level destructure.
        not_a_definition,
        /// `Code.type_id` of a proxy whose type the call leaves open, or
        /// fixes to a type that is no nominal.
        not_nominal,
        /// `Code.ty_of` of a proxy whose type the call leaves open, or that
        /// the walk has no description for.
        rejected: Rejection,
    },
};

/// The constant each `Code.prim`, `Code.type_id` and `Code.ty_of` call of
/// this module computes, written into `store` as the value of a
/// `Code.PrimId`, a `Code.TypeId` or a `Code.Ty`, in node order. A
/// `Code.prim` id is the id a `Prim` node carries for the same definition
/// (`reify.identity.prim`), a `Code.type_id` id the one an `Opaque` of the
/// same nominal carries, and a `Code.ty_of` description the `result` of
/// `|x| x` at the proxy's type. A call of a template's inventory is
/// described at each closing use instead (D1, Q8): it has no outcome here.
/// A call the module's inventories refused has its refusal as its outcome.
/// The description step runs this. The caller owns the slice.
pub fn describeIdentities(gpa: Allocator, store: *ConstStore, inputs: ModuleInputs) Allocator.Error![]IdentityOutcome {
    const env = inputs.env();
    const uses = env.store.codeIdentityUses();
    if (uses.len == 0) return &.{};
    var walk = Walk.init(gpa, store, inputs.lookup);
    defer walk.deinit();
    const reader = try walk.reader(inputs);
    const inventories = try reader.codeInventories();

    var outcomes = std.ArrayList(IdentityOutcome).empty;
    errdefer outcomes.deinit(gpa);
    for (uses) |use| {
        const call: ExprId = @fromBackingInt(use.call);
        // A call checking rejected, or in code no body reaches, has no value
        // to take: it has no code-site bit.
        if (!reader.bodies.index().isCodeSite(call)) continue;
        // A call of a template's inventory is computed at each closing use.
        if (inventories.siteIndex(call) != null) continue;
        const arg: ExprId = @fromBackingInt(use.arg);
        const region = reader.bodies.expr(arg).source_region;
        if (inventoryRefusalOf(inventories, call)) |rejection| {
            try outcomes.append(gpa, .{ .call = call, .region = region, .outcome = .{ .rejected = rejection } });
            continue;
        }
        const outcome: @FieldType(IdentityOutcome, "outcome") = switch (use.kind) {
            .prim, .type_id => blk: {
                const bits = switch (use.kind) {
                    .prim => try reader.primIdentity(arg, @fromBackingInt(@intCast(use.arg))),
                    .type_id => reader.typeIdIdentity(arg),
                    .ty_of => unreachable, // the outer switch takes it
                };
                if (bits) |value| break :blk .{ .node = try store.append(.{ .record = &.{try store.append(.{ .scalar = .{ .u128 = value } })} }) };
                break :blk switch (use.kind) {
                    .prim => .not_a_definition,
                    .type_id => .not_nominal,
                    .ty_of => unreachable, // the outer switch takes it
                };
            },
            .ty_of => blk: {
                walk.beginSite(.graph, false, reader);
                try walk.startSite();
                break :blk switch (try reader.tyOfProxy(arg, region)) {
                    .reified => |node| .{ .node = node },
                    .rejected => |rejection| .{ .rejected = rejection },
                };
            },
        };
        try outcomes.append(gpa, .{ .call = call, .region = region, .outcome = outcome });
    }
    std.mem.sort(IdentityOutcome, outcomes.items, {}, identityOutcomeLessThan);
    return outcomes.toOwnedSlice(gpa);
}

fn identityOutcomeLessThan(_: void, a: IdentityOutcome, b: IdentityOutcome) bool {
    return @backingInt(a.call) < @backingInt(b.call);
}

/// The refusal a module's inventories hold for the site or identity call
/// `node`, or null.
fn inventoryRefusalOf(inventories: *const code_analyses.CodeInventories, node: ExprId) ?Rejection {
    const refusals = inventories.refusals;
    const index = std.sort.binarySearch(code_analyses.CodeInventories.Refusal, refusals, node, struct {
        fn order(key: ExprId, item: code_analyses.CodeInventories.Refusal) std.math.Order {
            return std.math.order(@backingInt(key), @backingInt(item.node));
        }
    }.order) orelse return null;
    return refusals[index].rejection;
}

/// The description step's walk of one module's sites and closing uses (D1).
/// The two share one walk, so a description a closing use builds again is
/// the node a site wrote.
///
/// The step calls `describeSites`, then `closeUses`, then `takeProvenance`.
pub const Description = struct {
    gpa: Allocator,
    walk: Walk,
    reader: *Reifier,
    inputs: DescribeInputs,
    /// The module's inventories, from its `codeInventories` slot.
    inventories: *const code_analyses.CodeInventories,
    /// Every site and use of every body of the module.
    scan: ModuleScan,

    /// Open the walk of one module, whose descriptions are written into
    /// `store`. The caller owns the result.
    pub fn init(gpa: Allocator, store: *ConstStore, inputs: DescribeInputs) Allocator.Error!*Description {
        const self = try gpa.create(Description);
        errdefer gpa.destroy(self);
        self.* = .{
            .gpa = gpa,
            .walk = Walk.init(gpa, store, inputs.module.lookup),
            .reader = undefined,
            .inputs = inputs,
            .inventories = undefined,
            .scan = .{},
        };
        errdefer self.walk.deinit();
        self.reader = try self.walk.reader(inputs.module);
        self.inventories = try self.reader.codeInventories();
        self.scan = try ModuleScan.collect(gpa, self.reader);
        return self;
    }

    pub fn deinit(self: *Description) void {
        const gpa = self.gpa;
        self.scan.deinit(gpa);
        self.walk.deinit();
        gpa.destroy(self);
    }

    /// Walk every site of the module that is described in it, one outcome
    /// per site, in node order (the order the site loop counts first slots
    /// in). A site the module's inventories refused has that refusal as its
    /// outcome. An instance site has none: each closing use describes it.
    /// The caller owns the slice.
    pub fn describeSites(self: *Description) Allocator.Error![]SiteOutcome {
        const gpa = self.gpa;
        const walk = &self.walk;
        const reifier = self.reader;
        const env = reifier.env;
        // Node order, the order the inventories count a bound call's sites
        // in.
        const sites = try gpa.dupe(CodeSiteRecord, env.store.codeReificationSites());
        defer gpa.free(sites);
        std.mem.sort(CodeSiteRecord, sites, {}, siteRecordLessThan);

        var results = std.ArrayList(SiteOutcome).empty;
        errdefer {
            for (results.items) |outcome| {
                freeSlotSources(gpa, outcome.slots);
                gpa.free(outcome.reads);
            }
            results.deinit(gpa);
        }
        var call_args = std.ArrayList(ExprId).empty;
        defer call_args.deinit(gpa);
        var call_values = std.ArrayList(Reifier.TemplateArg).empty;
        defer call_values.deinit(gpa);

        // The slots of each binding call's sites walked so far, which give
        // the next site of that call its first slot (site order).
        var call_slots = std.AutoHashMapUnmanaged(u32, u64).empty;
        defer call_slots.deinit(gpa);

        for (sites) |site| {
            // A template and the name a template call calls both stand for a
            // description built elsewhere, so nothing is walked for either: the
            // node keeps the empty description body copying left on it.
            switch (site.kind) {
                .template, .template_callee => continue,
                .named_function, .inline_lambda, .template_call, .value => {},
            }
            const site_expr: ExprId = @fromBackingInt(site.node_idx);
            // A site checking replaced, or in code no body reaches, has no
            // code-site bit and no description.
            if (!reifier.bodies.index().isCodeSite(site_expr)) continue;
            // An instance site is described at each closing use.
            if (self.inventories.siteIndex(site_expr) != null) continue;
            const region = env.store.getRegionAt(@fromBackingInt(@intCast(site.node_idx)));
            if (inventoryRefusalOf(self.inventories, site_expr)) |rejection| {
                try results.append(gpa, .{ .expr = site_expr, .region = region, .outcome = .{ .rejected = rejection } });
                continue;
            }
            const bound_call: ?u32 = if (site.bound_call == CodeSiteRecord.no_bound_call) null else site.bound_call;
            // `ROC_REIFY_OUTLINE_STATS`: the site walked once per K it lists,
            // each walk measured and dropped, before the walk that counts.
            if (base.dev_diagnostics.items(.reify_outline_stats)) |list| {
                var ks = list;
                while (ks.next()) |text| {
                    const k = std.fmt.parseInt(u32, text, 10) catch continue;
                    if (k < 3) continue;
                    walk.beginSite(site.view, bound_call != null, reifier);
                    try useSiteCut(walk, reifier, site);
                    if (bound_call != null) walk.useCaptureReads(try captureReads(gpa, reifier, site_expr));
                    walk.measure_k = k;
                    defer walk.measure_k = null;
                    _ = try walkSite(gpa, walk, reifier, site, site_expr, region, &call_args, &call_values);
                    freeSlotSources(gpa, walk.takeSlots());
                    gpa.free(try walk.takeReads());
                }
            }
            walk.beginSite(site.view, bound_call != null, reifier);
            try useSiteCut(walk, reifier, site);
            if (bound_call != null) walk.useCaptureReads(try captureReads(gpa, reifier, site_expr));
            const earlier_slots = if (bound_call) |call| try call_slots.getOrPut(gpa, call) else null;
            if (earlier_slots) |entry| {
                if (!entry.found_existing) entry.value_ptr.* = 0;
                walk.first_slot = entry.value_ptr.*;
            }
            const outcome = try walkSite(gpa, walk, reifier, site, site_expr, region, &call_args, &call_values);
            const slots = walk.takeSlots();
            errdefer freeSlotSources(gpa, slots);
            if (earlier_slots) |entry| entry.value_ptr.* += slots.len;
            const reads = try walk.takeReads();
            errdefer gpa.free(reads);
            try results.append(gpa, .{ .expr = site_expr, .region = region, .outcome = outcome, .slots = slots, .bound_call = bound_call, .chain_stop = site.chain_stop, .chain_end = if (site.chain_end == CodeSiteRecord.no_chain_end) null else @fromBackingInt(site.chain_end), .bound_root = site.bound_root, .reads = reads });
        }

        return results.toOwnedSlice(gpa);
    }

    /// Build the table of each closing use of the module, in node order,
    /// and of each platform requirement it satisfies, by requires index.
    /// The caller owns the result.
    pub fn closeUses(self: *Description) Allocator.Error!ClosedUses {
        const gpa = self.gpa;
        var tables = TableBuilder{ .gpa = gpa, .walk = &self.walk, .reifier = self.reader, .requirements = self.inputs.requirement_uses };
        defer tables.deinit();
        var refused = std.ArrayList(RefusedUse).empty;
        defer refused.deinit(gpa);
        var edges = std.ArrayList(ClosedEdge).empty;
        defer edges.deinit(gpa);
        // The written uses are this module's source, so a refusal is placed here.
        self.walk.body = self.reader;
        try closeWrittenUses(&tables, &self.scan, self.inputs.roots, &edges, &refused);
        var refused_implicits = std.ArrayList(RefusedImplicit).empty;
        defer refused_implicits.deinit(gpa);
        try closeImplicits(&tables, &self.scan, &refused_implicits);
        try closeRequirements(&tables, self.inputs.roots, &edges, &refused);
        try closeEvidenceEdges(&tables, &self.scan, self.inputs.roots, &edges, &refused);
        // Each root of a generic bound call has its closing use, a written
        // use or a platform requirement, which either binds the call's
        // inputs or is refused, so checking fails.
        if (std.debug.runtime_safety and refused.items.len == 0) {
            for (self.inputs.roots) |root| {
                const argument = root.literal_argument orelse continue;
                if (argument.site.kind != .bound_call) continue;
                for (tables.root_bounds.items) |bound| {
                    if (bound.root == root.id) break;
                } else invariant("a generic bound call's root has no closing use that binds its inputs");
            }
        }
        std.mem.sort(ClosedEdge, edges.items, {}, closedEdgeLessThan);
        var result: ClosedUses = .{};
        errdefer result.deinit(gpa);
        // An implicit instance of a refused table is refused: lowering
        // crashes where the compiler would call the method.
        result.implicit_refused = try gpa.alloc(bool, tables.implicit_instances.items.len);
        for (tables.implicit_instances.items, result.implicit_refused) |instance, *is_refused| {
            is_refused.* = (try tables.firstRejection(instance.table)) != null;
        }
        result.tables = try tables.finish();
        result.edges = try edges.toOwnedSlice(gpa);
        result.refused = try refused.toOwnedSlice(gpa);
        result.refused_implicits = try refused_implicits.toOwnedSlice(gpa);
        return result;
    }

    /// The provenance of every description the walk wrote. The caller owns
    /// the slice.
    pub fn takeProvenance(self: *Description) Allocator.Error![]SiteProvenance {
        return self.walk.published.toOwnedSlice(self.gpa);
    }
};

fn siteRecordLessThan(_: void, a: CodeSiteRecord, b: CodeSiteRecord) bool {
    return a.node_idx < b.node_idx;
}

fn closedEdgeLessThan(_: void, a: ClosedEdge, b: ClosedEdge) bool {
    return CodeEdgeKey.lessThan({}, CodeEdgeKey.of(a.edge), CodeEdgeKey.of(b.edge));
}

/// Whether `id` mentions a variable of `vars`, read as `Reifier.mentionsAny`
/// reads it: an undetermined field kind is a variable it mentions. Publication
/// reads it too, to find the generic bound calls (design.md "Bound Instance
/// Roots"), so the two cannot disagree.
pub fn typeMentionsIn(gpa: Allocator, types: checked.CheckedTypeStoreView, id: CheckedTypeId, vars: *const MentionVars, seen: *MentionVars) Allocator.Error!bool {
    // Keyed by id: `seen` only stops a revisit, and a variable's id is the
    // root of its solver variable, so `vars` names it by that one id.
    if ((try seen.getOrPut(gpa, id)).found_existing) return false;
    switch (types.payload(id)) {
        .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
        .flex, .rigid => |variable| {
            if (vars.contains(id)) return true;
            var constraints = variable.constraints.iterator();
            while (constraints.next()) |constraint| if (try typeMentionsIn(gpa, types, constraint.fn_ty, vars, seen)) return true;
            return false;
        },
        .alias => |alias| return typeMentionsIn(gpa, types, alias.backing, vars, seen),
        .function => |fn_ty| {
            for (fn_ty.args) |arg| if (try typeMentionsIn(gpa, types, arg, vars, seen)) return true;
            return typeMentionsIn(gpa, types, fn_ty.ret, vars, seen);
        },
        .nominal => |nominal| {
            for (nominal.args) |arg| if (try typeMentionsIn(gpa, types, arg, vars, seen)) return true;
            return false;
        },
        .tuple => |parts| {
            for (parts) |part| if (try typeMentionsIn(gpa, types, part, vars, seen)) return true;
            return false;
        },
        .record => |record| {
            var fields = record.fields.iterator();
            while (fields.next()) |field| {
                // A kind a substitution committed (a type that
                // `cloneCheckedTypeRootSubstituting` built) mentions nothing.
                if (field.kind.undeterminedVariable()) |kind| if (types.payload(kind) != .field_kind) {
                    if (try typeMentionsIn(gpa, types, kind, vars, seen)) return true;
                };
                if (try typeMentionsIn(gpa, types, field.ty, vars, seen)) return true;
            }
            return typeMentionsIn(gpa, types, record.ext, vars, seen);
        },
        .tag_union => |union_ty| {
            var variants = union_ty.tags.iterator();
            while (variants.next()) |variant| {
                for (variant.args) |arg| if (try typeMentionsIn(gpa, types, arg, vars, seen)) return true;
            }
            return typeMentionsIn(gpa, types, union_ty.ext, vars, seen);
        },
        .empty_record, .empty_tag_union, .pending, .err => return false,
    }
}

/// A set of type variables, as `typeMentionsIn` reads it.
pub const MentionVars = collections.DenseMapUnmanaged(CheckedTypeId, void);

const CodeSiteRecord = @import("can").NodeStore.CodeReificationSite;
const CodeEdge = code_output.CodeEdge;
const CodeEdgeKey = code_output.EdgeKey;
const Inventories = code_analyses.CodeInventories;

/// A platform requirement of an app module as a closing use of its app
/// binding (design.md "Code Instance Tables"): the binding instantiated at
/// the requirement's solution with each free variable sealed as lowering
/// seals it.
pub const RequirementUse = struct {
    requires_idx: u32,
    binding: checked.ArtifactTopLevelProcedureBindingRef,
    binder: BinderId,
    /// The binding's definition, where the report of a refused use stands.
    body: ExprId,
    /// The sealed solution, or null where a free variable of the solution
    /// has a constraint that sealing would ignore: the use is refused.
    sealed: ?CheckedTypeId,
    /// The requirement's root-call dispatch evidence, a span of this
    /// module's `evidence_refs`.
    evidence: artifact_serialize.Span,
};

/// A closing use refused (D1): the key lowering finds the refusal by, the
/// expression a crash replaces, the use's region, where the report stands,
/// and the refusal.
pub const RefusedUse = struct {
    /// The closing edge, the key of its entry in the module's `CodeOutput`:
    /// a written use (a `for` loop's `iter` use by the loop's body), or a
    /// platform requirement.
    edge: CodeEdge,
    /// The expression a crash replaces: the call a callee lookup is the
    /// callee of, the use itself, or a requirement's binding definition.
    expr: ExprId,
    /// For a `for` statement's `iter` use, the statement (see `Occurrence`).
    statement: ?StatementId = null,
    region: base.Region,
    rejection: Rejection,
};

/// One site or use a body holds, as the inventory and the closing uses read
/// them (D1).
const Occurrence = struct {
    /// A `Code` site, a use of a procedure, or a `Code.type_id` or
    /// `Code.ty_of` call, which is described as a site is (Q8, D6).
    kind: enum { site, use, identity },
    expr: ExprId,
    /// The expression a refused use makes a runtime error: the call a callee
    /// lookup is the callee of, or the use itself.
    poison: ExprId,
    /// The template whose body holds it, or null for a body of no template
    /// of this module.
    template: ?canonical.CheckedProcedureTemplateId,
    /// Whether its type mentions a quantified variable of `template`.
    template_vars: bool,
    /// Whether its type mentions a quantified variable of a lambda a block
    /// inside the body generalized (Q5).
    local_vars: bool,
    /// The `for` statement a refused `iter` use makes a runtime error, where
    /// the loop is a statement: it has no expression of its own.
    statement: ?StatementId = null,
    /// The expression a report about the use points at, where it is not
    /// `expr`: for a `for` loop's `iter` use, the iterable.
    shown: ?ExprId = null,
    /// For a use, the edge its table is keyed by (design.md "Code Instance
    /// Tables"): the use itself, or, for a static dispatch, the evidence
    /// node the call targets directly.
    edge: CodeEdge,
};

fn occurrenceLessThan(_: void, a: Occurrence, b: Occurrence) bool {
    return @backingInt(a.expr) < @backingInt(b.expr);
}

/// One site of a generic bound call while its template's inventory is
/// built: the site's node, its inventory index, and its recipe.
const BoundMember = struct {
    raw_call: u32,
    node_idx: u32,
    index: u32,
    recipe: u32,

    fn lessThan(_: void, a: BoundMember, b: BoundMember) bool {
        if (a.raw_call != b.raw_call) return a.raw_call < b.raw_call;
        return a.node_idx < b.node_idx;
    }
};

fn rootBoundLessThan(_: void, a: InstanceTables.RootBound, b: InstanceTables.RootBound) bool {
    return @backingInt(a.root) < @backingInt(b.root);
}

fn indexedLessThan(_: void, a: Inventories.Indexed, b: Inventories.Indexed) bool {
    return @backingInt(a.node) < @backingInt(b.node);
}

fn refusalLessThan(_: void, a: Inventories.Refusal, b: Inventories.Refusal) bool {
    return @backingInt(a.node) < @backingInt(b.node);
}

/// What a body walk reads for each site: its record and its `f`.
const SiteInfo = struct {
    record: CodeSiteRecord,
    fn_ty: CheckedTypeId,
};

/// The `f` of a site's `Code(f)`, the type the checker recorded for the site.
fn siteFnType(reifier: *const Reifier, site: CodeSiteRecord) CheckedTypeId {
    return reifier.bodies.typeOf(@fromBackingInt(site.fn_var));
}

/// A `Code.type_id` or `Code.ty_of` call a body walk reads: its argument,
/// whose type is the proxy's, and which of the two it is.
const IdentityInfo = struct {
    arg: ExprId,
    kind: Inventories.RecipeKind,
};

const IdentityMap = collections.DenseMapUnmanaged(ExprId, IdentityInfo);

/// Every site and use of every body of one module, as the inventories and
/// the closing uses read them (D1). `planModule` and the description step
/// each collect it: it is a pure function of the module's checked data.
const ModuleScan = struct {
    site_map: collections.DenseMapUnmanaged(ExprId, SiteInfo) = .empty,
    identity_map: IdentityMap = .empty,
    /// Every site and use of every body, in body order.
    occurrences: std.ArrayList(Occurrence) = .empty,
    /// Each descriptor method of this module that a generic bound call
    /// makes refused, at the method (Q17).
    refused_methods: std.ArrayList(code_analyses.CodeInventories.RefusedMethod) = .empty,
    /// Each type occurrence of a nominal whose descriptor method's target
    /// is a template that can hold an inventory, in body order (Q17).
    implicits: std.ArrayList(ImplicitOccurrence) = .empty,
    /// The owner types of `implicits`.
    terms: TermPool = .{},
    /// Each edge that the evidence of a use reaches, once, in body order.
    edges: std.ArrayList(EdgeOccurrence) = .empty,

    fn deinit(self: *ModuleScan, gpa: Allocator) void {
        self.site_map.deinit(gpa);
        self.identity_map.deinit(gpa);
        self.occurrences.deinit(gpa);
        self.edges.deinit(gpa);
        self.refused_methods.deinit(gpa);
        self.implicits.deinit(gpa);
        self.terms.deinit(gpa);
    }

    fn collect(gpa: Allocator, reifier: *Reifier) Allocator.Error!ModuleScan {
        var scan = ModuleScan{};
        errdefer scan.deinit(gpa);
        const bodies = reifier.bodies;
        for (reifier.env.store.codeIdentityUses()) |use| {
            const kind: Inventories.RecipeKind = switch (use.kind) {
                // A `Code.prim` reference is not instantiated, so its id never
                // depends on a use.
                .prim => continue,
                .type_id => .type_id,
                .ty_of => .ty_of,
            };
            const call: ExprId = @fromBackingInt(use.call);
            // A call checking rejected is no code site.
            if (!bodies.index().isCodeSite(call)) continue;
            try scan.identity_map.put(gpa, call, .{ .arg = @fromBackingInt(use.arg), .kind = kind });
        }
        for (reifier.env.store.codeReificationSites()) |site| {
            const expr: ExprId = @fromBackingInt(site.node_idx);
            // A site checking replaced is no code site.
            if (!bodies.index().isCodeSite(expr)) continue;
            try scan.site_map.put(gpa, expr, .{ .record = site, .fn_ty = siteFnType(reifier, site) });
        }
        // A descriptor method can be bound to a template of another module,
        // whatever this module holds.
        try refusedMethods(gpa, reifier, &scan);
        // A module with no site and no identity call closes a use only of a
        // template an import holds an inventory for, so with no such import
        // it has no occurrence to scan.
        if (scan.site_map.count() == 0 and scan.identity_map.count() == 0 and !try importsHoldInventories(reifier)) return scan;
        // The type occurrences of the descriptor methods (Q17) are read in
        // the same bodies, by the same walk.
        var implicit_scan = ImplicitScan{ .r = reifier, .terms = &scan.terms, .out = &scan.implicits, .own_refused = &scan.refused_methods };
        defer implicit_scan.deinit();
        // The edges of the uses' evidence are read in the same bodies too.
        var edge_scan = EdgeScan{ .walk = .{ .allocator = gpa, .plans = reifier.plans }, .out = &scan.edges };
        defer edge_scan.walk.deinit();

        // Every procedure body of this module, once: its sites and the uses
        // it makes.
        for (reifier.procedure_templates.templates.items) |template| {
            const root_expr = switch (template.body) {
                .checked_body => |root_expr| root_expr,
                .intrinsic_wrapper, .entry_wrapper, .unimplemented => continue,
            };
            var template_vars: Reifier.RowVars = .empty;
            defer template_vars.deinit(gpa);
            for (reifier.schemeVars(template)) |scheme_var| try template_vars.put(gpa, scheme_var, {});
            var body_scan = OccurrenceScan{
                .r = reifier,
                .sites = &scan.site_map,
                .identities = &scan.identity_map,
                .template = template.template_id,
                .template_vars = &template_vars,
                .out = &scan.occurrences,
                .implicit = &implicit_scan,
                .edges = &edge_scan,
            };
            defer body_scan.local_vars.deinit(gpa);
            try body_scan.expr(root_expr, null);
        }
        // A compile-time constant, and a top-level binding whose value
        // evaluation computes, is no procedure body (Q16). A use in it at a
        // variable of the binding's own type is at a quantified variable, which
        // a use of the binding fixes; any other use is a closing use. An
        // expression a body above already holds is not recorded again.
        for (reifier.const_bodies.bodies) |const_body| {
            // A constant evaluation computes at each type a use fixes runs an
            // entry template, whose variables are the constant's: a use at them
            // is a forward entry of that template's inventory.
            if (constantEntryTemplate(reifier, const_body.id)) |entry| {
                var entry_vars: Reifier.RowVars = .empty;
                defer entry_vars.deinit(gpa);
                for (reifier.schemeVars(reifier.procedure_templates.templates.items[@backingInt(entry)])) |scheme_var| try entry_vars.put(gpa, scheme_var, {});
                var body_scan = OccurrenceScan{ .r = reifier, .sites = &scan.site_map, .identities = &scan.identity_map, .template = entry, .template_vars = &entry_vars, .out = &scan.occurrences, .implicit = &implicit_scan, .edges = &edge_scan };
                defer body_scan.local_vars.deinit(gpa);
                try body_scan.expr(const_body.body_expr, null);
                continue;
            }
            try scanBinding(gpa, reifier, &scan.site_map, &scan.identity_map, &scan.occurrences, &implicit_scan, &edge_scan, const_body.checked_type, const_body.body_expr);
        }
        for (reifier.callable_eval_templates.templates) |eval_template| {
            // A binding that computes a function is computed by its entry
            // wrapper at each type a use fixes, as such a constant is: a use
            // at the wrapper's variables is a forward entry of its inventory.
            // An exact alias is no such binding: a use of it reaches the
            // procedure its lookup names.
            if (eval_template.forwarded_lookup == null) {
                const wrapper = reifier.entry_wrappers.lookupByRoot(eval_template.root) orelse
                    invariant("a binding that computes a function has no entry wrapper");
                const entry = wrapper.template.template;
                var entry_vars: Reifier.RowVars = .empty;
                defer entry_vars.deinit(gpa);
                for (reifier.schemeVars(reifier.procedure_templates.templates.items[@backingInt(entry)])) |scheme_var| try entry_vars.put(gpa, scheme_var, {});
                var body_scan = OccurrenceScan{ .r = reifier, .sites = &scan.site_map, .identities = &scan.identity_map, .template = entry, .template_vars = &entry_vars, .out = &scan.occurrences, .implicit = &implicit_scan, .edges = &edge_scan };
                defer body_scan.local_vars.deinit(gpa);
                try body_scan.expr(eval_template.body, null);
                continue;
            }
            try scanBinding(gpa, reifier, &scan.site_map, &scan.identity_map, &scan.occurrences, &implicit_scan, &edge_scan, eval_template.checked_fn_root, eval_template.body);
        }
        // A top-level `expect` is a compile-time root that no use reaches and
        // that quantifies no variable, so each use in it is a closing use.
        const no_vars: Reifier.RowVars = .empty;
        for (reifier.env.store.sliceStatements(reifier.env.all_statements)) |statement_idx| {
            const statement = reifier.env.store.getStatement(statement_idx);
            if (statement != .s_expect) continue;
            var body_scan = OccurrenceScan{ .r = reifier, .sites = &scan.site_map, .identities = &scan.identity_map, .template = null, .template_vars = &no_vars, .out = &scan.occurrences, .implicit = &implicit_scan, .edges = &edge_scan };
            defer body_scan.local_vars.deinit(gpa);
            try body_scan.expr(statement.s_expect.body, null);
        }
        try dedupeOccurrences(gpa, &scan.occurrences);
        try dedupeEdges(gpa, &scan.edges);
        return scan;
    }
};

/// The inventories of a module's templates (D1), and the refusals of the
/// instance sites and identity calls that no closing use can describe. The
/// module's `codeInventories` slot computes this. It writes no description,
/// and reads the inventories of imported modules through their slots.
pub fn planModule(gpa: Allocator, inputs: PlanInputs) Allocator.Error!*code_analyses.CodeInventories {
    var walk = Walk.init(gpa, null, inputs.lookup);
    defer walk.deinit();
    const reifier = try walk.reader(inputs);
    reifier.planning = true;
    // Planning reads this module's uses, so a refusal is placed here.
    walk.body = reifier;
    var scan = try ModuleScan.collect(gpa, reifier);
    defer scan.deinit(gpa);
    var call_args = std.ArrayList(ExprId).empty;
    defer call_args.deinit(gpa);
    return planInstances(gpa, &walk, reifier, &scan, &call_args);
}

/// The inventories of this module's templates (D1), and the refusals of
/// instance sites that no closing use can describe. The caller owns the
/// result.
fn planInstances(
    gpa: Allocator,
    walk: *Walk,
    reifier: *Reifier,
    scan: *ModuleScan,
    call_args: *std.ArrayList(ExprId),
) Allocator.Error!*code_analyses.CodeInventories {
    var refusals = std.ArrayList(Inventories.Refusal).empty;
    defer refusals.deinit(gpa);

    // A generic bound call binds its inputs at each closing use, so each of
    // its sites is described there too, as an instance site is, whatever its
    // own type. Publication decided which calls are generic: each is an own
    // bound requirement of the scheme around it (design.md "Bound Instance
    // Roots").
    var generic_bound: collections.DenseMapUnmanaged(u32, void) = .empty;
    defer generic_bound.deinit(gpa);
    {
        var own_calls: collections.DenseMapUnmanaged(u32, void) = .empty;
        defer own_calls.deinit(gpa);
        const templates = reifier.procedure_templates;
        for (templates.templates.items) |*template| {
            for (templates.templateLiteralRequirements(template)) |requirement| {
                if (requirement.edge == .literal and requirement.site.kind == .bound_call) try own_calls.put(gpa, requirement.site.node, {});
            }
        }
        for (templates.dispatch_scopes) |*scope| {
            for (templates.scopeLiteralRequirements(scope)) |requirement| {
                if (requirement.edge == .literal and requirement.site.kind == .bound_call) try own_calls.put(gpa, requirement.site.node, {});
            }
        }
        for (reifier.env.store.codeReificationSites()) |site| {
            if (site.bound_call == CodeSiteRecord.no_bound_call) continue;
            if (own_calls.contains(site.bound_call)) try generic_bound.put(gpa, site.bound_call, {});
        }
    }
    for (scan.occurrences.items) |*occurrence| {
        if (occurrence.kind != .site) continue;
        if (generic_bound.contains(scan.site_map.get(occurrence.expr).?.record.bound_call)) occurrence.template_vars = true;
    }

    // A template has an inventory when it holds an instance site, or a use
    // at its own variables of a template that has one. Uses reach other
    // templates of this module, so this is a fixpoint.
    var holders: collections.DenseMapUnmanaged(canonical.CheckedProcedureTemplateId, void) = .empty;
    defer holders.deinit(gpa);
    for (scan.occurrences.items) |occurrence| {
        if (occurrence.kind == .use or !occurrence.template_vars) continue;
        // A site in a binding that is no procedure is described once.
        const holder = occurrence.template orelse continue;
        try holders.put(gpa, holder, {});
    }
    while (true) {
        var grew = false;
        for (scan.occurrences.items) |occurrence| {
            if (occurrence.kind != .use or !occurrence.template_vars or occurrence.local_vars) continue;
            // A binding that is no procedure has no inventory: a use of it
            // closes through the binding (Q16).
            if (occurrence.template == null) continue;
            if (holders.contains(occurrence.template.?)) continue;
            if (!try usedHasInventory(reifier, &holders, occurrence.expr)) continue;
            try holders.put(gpa, occurrence.template.?, {});
            grew = true;
        }
        // So is an edge of a use's evidence at the template's variables
        // whose target has an inventory.
        for (scan.edges.items) |occurrence| {
            if (!occurrence.template_vars or occurrence.local_vars) continue;
            const holder = occurrence.template orelse continue;
            if (holders.contains(holder)) continue;
            if (!try edgeHasInventory(reifier, &holders, occurrence.edge)) continue;
            try holders.put(gpa, holder, {});
            grew = true;
        }
        // A type occurrence at the template's variables of a descriptor
        // method whose target has an inventory is an entry too (Q17).
        for (scan.implicits.items) |occurrence| {
            if (!occurrence.template_vars or occurrence.local_vars) continue;
            const holder = occurrence.template orelse continue;
            if (holders.contains(holder)) continue;
            if (!try implicitTargetHasInventory(reifier, &holders, occurrence.target)) continue;
            try holders.put(gpa, holder, {});
            grew = true;
        }
        if (!grew) break;
    }

    var inventories = std.ArrayList(Inventories.Inventory).empty;
    defer inventories.deinit(gpa);
    var entries = std.ArrayList(Inventories.Entry).empty;
    defer entries.deinit(gpa);
    var indexed_sites = std.ArrayList(Inventories.Indexed).empty;
    defer indexed_sites.deinit(gpa);
    var forwards = std.ArrayList(Inventories.IndexedEdge).empty;
    defer forwards.deinit(gpa);
    var forward_edges = std.ArrayList(CodeEdge).empty;
    defer forward_edges.deinit(gpa);
    var recipes = RecipeBuilder{ .gpa = gpa };
    defer recipes.deinit();
    var bound_call_records = std.ArrayList(Inventories.BoundCall).empty;
    defer bound_call_records.deinit(gpa);
    var implicits = std.ArrayList(Inventories.Implicit).empty;
    defer implicits.deinit(gpa);
    var bound_sites = std.ArrayList(u32).empty;
    defer bound_sites.deinit(gpa);
    var bound_leaves: std.ArrayListUnmanaged(BinderId) = .empty;
    defer bound_leaves.deinit(gpa);
    var call_leaves: std.ArrayListUnmanaged(BinderId) = .empty;
    defer call_leaves.deinit(gpa);
    var members = std.ArrayList(BoundMember).empty;
    defer members.deinit(gpa);
    // The generic bound calls one of whose sites has no recipe.
    var unrecipied: collections.DenseMapUnmanaged(u32, void) = .empty;
    defer unrecipied.deinit(gpa);

    // One inventory per holder, its entries in body order.
    var ordered = std.ArrayList(canonical.CheckedProcedureTemplateId).empty;
    defer ordered.deinit(gpa);
    var key_iterator = holders.keyIterator();
    while (key_iterator.next()) |template_id| try ordered.append(gpa, template_id.*);
    std.mem.sort(canonical.CheckedProcedureTemplateId, ordered.items, {}, templateIdLessThan);
    for (ordered.items) |template_id| {
        const start: u32 = @intCast(entries.items.len);
        members.clearRetainingCapacity();
        unrecipied.clearRetainingCapacity();
        for (scan.occurrences.items) |occurrence| {
            if (occurrence.template == null or occurrence.template.? != template_id) continue;
            if (!occurrence.template_vars) continue;
            const index: u32 = @as(u32, @intCast(entries.items.len)) - start;
            switch (occurrence.kind) {
                .site => {
                    const info = scan.site_map.get(occurrence.expr).?;
                    const region = reifier.env.store.getRegionAt(@fromBackingInt(info.record.node_idx));
                    // A generic bound call binds its sites' inputs at each
                    // closing use (R7). Any other call that binds a site
                    // here reads a run-time value outside its sites, so no
                    // closing use can make it a root.
                    const bound_raw = info.record.bound_call;
                    const generic_bound_site = bound_raw != CodeSiteRecord.no_bound_call and generic_bound.contains(bound_raw);
                    if (bound_raw != CodeSiteRecord.no_bound_call and !generic_bound_site) {
                        try refusals.append(gpa, .{ .node = occurrence.expr, .rejection = .{
                            .kind = .bound_instance,
                            .region = region,
                            .module = reifier.rejectionModule(),
                            .detail = "",
                        } });
                        continue;
                    }
                    const recipe = switch (try recipes.resolve(walk, reifier, info, occurrence.expr, region, call_args)) {
                        .recipe => |recipe| recipe,
                        .rejected => |rejection| {
                            if (generic_bound_site) try unrecipied.put(gpa, bound_raw, {});
                            try refusals.append(gpa, .{ .node = occurrence.expr, .rejection = rejection });
                            continue;
                        },
                    };
                    if (generic_bound_site) {
                        try members.append(gpa, .{ .raw_call = bound_raw, .node_idx = info.record.node_idx, .index = index, .recipe = recipe });
                    }
                    try indexed_sites.append(gpa, .{ .node = occurrence.expr, .index = index });
                    try entries.append(gpa, .{ .kind = .site, .node = occurrence.expr, .recipe = recipe });
                },
                // A `Code.type_id` or `Code.ty_of` call is computed at each
                // closing use, as an instance site is described (Q8, D6).
                .identity => {
                    const info = scan.identity_map.get(occurrence.expr).?;
                    const arg = reifier.bodies.expr(info.arg);
                    try recipes.recipes.append(gpa, .{
                        .kind = info.kind,
                        .view = .graph,
                        .fn_ty = arg.ty,
                        .region = arg.source_region,
                        .root_module = Inventories.none,
                        .root_body = info.arg,
                        .scheme_vars = .{},
                        .scheme_root = null,
                        .in_block = false,
                        .use = null,
                        .translator = null,
                        .args = .{},
                    });
                    try indexed_sites.append(gpa, .{ .node = occurrence.expr, .index = index });
                    try entries.append(gpa, .{ .kind = .site, .node = occurrence.expr, .recipe = @intCast(recipes.recipes.items.len - 1) });
                },
                .use => {
                    if (occurrence.local_vars) continue;
                    if (!try usedHasInventory(reifier, &holders, occurrence.expr)) continue;
                    try forwards.append(gpa, .{ .edge = occurrence.edge, .index = index });
                    try entries.append(gpa, .{ .kind = .forward, .node = occurrence.expr, .recipe = @intCast(forward_edges.items.len) });
                    try forward_edges.append(gpa, occurrence.edge);
                },
            }
        }
        // Each edge of a use's evidence at the template's variables: its
        // table at the types each closing use fixes.
        for (scan.edges.items) |occurrence| {
            if (occurrence.template == null or occurrence.template.? != template_id) continue;
            if (!occurrence.template_vars or occurrence.local_vars) continue;
            if (!try edgeHasInventory(reifier, &holders, occurrence.edge)) continue;
            try forwards.append(gpa, .{ .edge = occurrence.edge, .index = @as(u32, @intCast(entries.items.len)) - start });
            try entries.append(gpa, .{ .kind = .forward, .node = occurrence.at, .recipe = @intCast(forward_edges.items.len) });
            try forward_edges.append(gpa, occurrence.edge);
        }
        // Each descriptor method at a type at the template's variables: its
        // table at the type each closing use fixes (Q17).
        for (scan.implicits.items) |occurrence| {
            if (occurrence.template == null or occurrence.template.? != template_id) continue;
            if (!occurrence.template_vars or occurrence.local_vars) continue;
            if (!try implicitTargetHasInventory(reifier, &holders, occurrence.target)) continue;
            try entries.append(gpa, .{ .kind = .implicit, .node = occurrence.expr, .recipe = @intCast(implicits.items.len) });
            try implicits.append(gpa, .{ .method = occurrence.method, .owner = occurrence.owner });
        }
        // The template's generic bound calls, each with its sites in site
        // order (node order, as the site loop counts first slots).
        const calls_start: u32 = @intCast(bound_call_records.items.len);
        std.mem.sort(BoundMember, members.items, {}, BoundMember.lessThan);
        var at: usize = 0;
        while (at < members.items.len) {
            const raw_call = members.items[at].raw_call;
            var end = at;
            while (end < members.items.len and members.items[end].raw_call == raw_call) end += 1;
            defer at = end;
            // A call one of whose sites has no recipe has no inputs to bind.
            if (unrecipied.contains(raw_call)) continue;
            const sites_start: u32 = @intCast(bound_sites.items.len);
            const call_index: u32 = @intCast(bound_call_records.items.len);
            call_leaves.clearRetainingCapacity();
            if (reifier.defining_statements == null) {
                reifier.defining_statements = try checked.boundLeafDefiningStatements(reifier.gpa, reifier.bodies);
            }
            const leaf_sources: checked.BoundLeafSources = .{
                .bodies = reifier.bodies,
                .types = reifier.types,
                .value_refs = reifier.value_refs,
                .defining_statements = &reifier.defining_statements.?,
            };
            for (members.items[at..end]) |member| {
                try bound_sites.append(gpa, member.index);
                recipes.recipes.items[member.recipe].bound = call_index;
                try checked.appendBoundSiteLeaves(gpa, leaf_sources, entries.items[start + member.index].node, &call_leaves, null);
            }
            const leaves_start: u32 = @intCast(bound_leaves.items.len);
            try bound_leaves.appendSlice(gpa, call_leaves.items);
            try bound_call_records.append(gpa, .{
                .call = @fromBackingInt(raw_call),
                .sites = .{ .start = sites_start, .len = @intCast(end - at) },
                .leaves = .{ .start = leaves_start, .len = @intCast(call_leaves.items.len) },
            });
        }
        try inventories.append(gpa, .{
            .template = template_id,
            .entries = .{ .start = start, .len = @as(u32, @intCast(entries.items.len)) - start },
            .bound_calls = .{ .start = calls_start, .len = @as(u32, @intCast(bound_call_records.items.len)) - calls_start },
        });
    }
    std.mem.sort(Inventories.Indexed, indexed_sites.items, {}, indexedLessThan);
    std.mem.sort(Inventories.IndexedEdge, forwards.items, {}, Inventories.IndexedEdge.lessThan);
    // A node that two method calls target, or that a call targets and the
    // evidence of another use reaches, is one edge with one table, so its
    // first entry serves each of them.
    {
        var kept: usize = 0;
        for (forwards.items) |forward| {
            if (kept != 0 and std.meta.eql(CodeEdgeKey.of(forwards.items[kept - 1].edge), CodeEdgeKey.of(forward.edge))) continue;
            forwards.items[kept] = forward;
            kept += 1;
        }
        forwards.shrinkRetainingCapacity(kept);
    }
    std.mem.sort(Inventories.Refusal, refusals.items, {}, refusalLessThan);

    const result = try gpa.create(code_analyses.CodeInventories);
    errdefer gpa.destroy(result);
    result.* = .{};
    errdefer freeInventories(gpa, result);
    result.inventories = try inventories.toOwnedSlice(gpa);
    result.entries = try entries.toOwnedSlice(gpa);
    result.sites = try indexed_sites.toOwnedSlice(gpa);
    result.forwards = try forwards.toOwnedSlice(gpa);
    result.forward_edges = try forward_edges.toOwnedSlice(gpa);
    result.recipes = try recipes.recipes.toOwnedSlice(gpa);
    result.scheme_vars = try recipes.scheme_vars.toOwnedSlice(gpa);
    result.args = try recipes.args.toOwnedSlice(gpa);
    result.modules = try recipes.modules.toOwnedSlice(gpa);
    result.bound_calls = try bound_call_records.toOwnedSlice(gpa);
    result.bound_sites = try bound_sites.toOwnedSlice(gpa);
    result.bound_leaves = try bound_leaves.toOwnedSlice(gpa);
    result.refusals = try refusals.toOwnedSlice(gpa);
    result.refused_methods = try gpa.dupe(code_analyses.CodeInventories.RefusedMethod, scan.refused_methods.items);
    result.implicits = try implicits.toOwnedSlice(gpa);
    result.terms = try scan.terms.toOwned(gpa);
    return result;
}

/// Free the slices of a `CodeInventories` that `planInstances` is part way
/// through filling. Each slice not yet taken is empty.
fn freeInventories(gpa: Allocator, result: *code_analyses.CodeInventories) void {
    gpa.free(result.inventories);
    gpa.free(result.entries);
    gpa.free(result.sites);
    gpa.free(result.forwards);
    gpa.free(result.forward_edges);
    gpa.free(result.recipes);
    gpa.free(result.scheme_vars);
    gpa.free(result.args);
    gpa.free(result.modules);
    gpa.free(result.bound_calls);
    gpa.free(result.bound_sites);
    gpa.free(result.bound_leaves);
    gpa.free(result.refusals);
    gpa.free(result.refused_methods);
    gpa.free(result.implicits);
    result.terms.deinit(gpa);
}

/// Whether the template `use` names has an inventory. A template of this
/// module has one when it is among `holders`, which `planInstances` is
/// building, so this module's own slot is never asked.
fn usedHasInventory(
    reifier: *Reifier,
    holders: *const collections.DenseMapUnmanaged(canonical.CheckedProcedureTemplateId, void),
    use: ExprId,
) Allocator.Error!bool {
    const used = try reifier.usedTemplate(use) orelse return false;
    if (used.reader == reifier) return holders.contains(used.template);
    return (try used.reader.codeInventories()).inventoryOf(used.template) != null;
}

/// Whether the template an edge of a use's evidence selects has an
/// inventory (`edgeTemplate`). A template of this module has one when it is
/// among `holders`, which `planInstances` is building.
fn edgeHasInventory(
    reifier: *Reifier,
    holders: ?*const collections.DenseMapUnmanaged(canonical.CheckedProcedureTemplateId, void),
    edge: CodeEdge,
) Allocator.Error!bool {
    const used = try edgeTemplate(reifier, edge) orelse return false;
    if (used.reader == reifier) if (holders) |planned| return planned.contains(used.template);
    return (try used.reader.codeInventories()).inventoryOf(used.template) != null;
}

/// The template an evidence node or a contract call selects, read as
/// `Reifier.methodTargetCallee` reads the target, or null for a target
/// with no body that can hold an inventory. A descriptor method is
/// described at the edge too; only a call the compiler makes by type, with
/// no edge, takes the table of its owner type's occurrence (Q17).
fn edgeTemplate(reifier: *Reifier, edge: CodeEdge) Allocator.Error!?Reifier.UsedTemplate {
    const node = reifier.plans.evidenceNode(switch (edge) {
        .node => |id| id,
        .derivation_call => |call| call.node,
        .use, .requirement, .literal => unreachable, // an edge of a use's evidence is a node or a contract call
    });
    const procedure = switch (node.target.kind) {
        .procedure => |procedure| procedure,
        .callable_binding => |binding| return try reifier.computedMethod(binding),
        .local_proc, .structural => return null,
    };
    // A method bound to another function by name has the definition in the
    // module of the target's template.
    const defining = if (node.target.alias != null)
        try reifier.templateReader(procedure.template.artifact) orelse return null
    else
        reifier;
    const def = try reifier.methodTargetDef(procedure, node.target) orelse return null;
    // An intrinsic has no body.
    if (try defining.intrinsicOfTemplate(procedure.template.artifact, def) != null) return null;
    const found = defining.methodDefinition(procedure.template, def) orelse return null;
    const reader = switch (found) {
        .provided => |builtin| try reifier.walk.reader(builtin.definition.module),
        .here, .here_builtin => defining,
        .away => |definition| try reifier.walk.reader(definition.module),
    };
    return .{ .reader = reader, .template = found.template().template_id, .body = found.body() };
}

/// Whether the template a descriptor method's type occurrence runs has an
/// inventory (Q17). A template of this module has one when it is among
/// `holders`, which `planInstances` is building.
fn implicitTargetHasInventory(
    reifier: *Reifier,
    holders: ?*const collections.DenseMapUnmanaged(canonical.CheckedProcedureTemplateId, void),
    target: ImplicitTarget,
) Allocator.Error!bool {
    if (std.meta.eql(target.artifact, reifier.artifact.bytes)) {
        if (holders) |planned| return planned.contains(target.template);
        return (try reifier.codeInventories()).inventoryOf(target.template) != null;
    }
    const reader = try reifier.templateReader(.{ .bytes = target.artifact }) orelse
        invariant("a descriptor method's target is a template of a module the walk cannot read");
    return (try reader.codeInventories()).inventoryOf(target.template) != null;
}

/// The descriptor methods of this module that a generic bound call makes
/// refused (Q17), read from the module's method registry.
fn refusedMethods(gpa: Allocator, reifier: *Reifier, scan: *ModuleScan) Allocator.Error!void {
    // A descriptor method whose scheme needs a generic bound call's input
    // binding is refused at the method: only a checked literal edge roots
    // such a call, and the compiler's own calls of the method have none
    // (Q17, design.md "Bound Instance Roots").
    for (reifier.sources.method_registry.entries) |entry| {
        const target = entry.target orelse continue;
        const method = DescriptorMethod.fromMethodName(reifier.names, entry.key.method) orelse continue;
        // Inspection calls only an eligible `to_inspect`.
        if (method == .to_inspect and entry.inspect_override == null) continue;
        const implicit = try implicitTargetOf(reifier, target) orelse continue;
        const holder = try reifier.templateReader(.{ .bytes = implicit.artifact }) orelse
            invariant("a descriptor method's target is a template of a module the walk cannot read");
        const templates = holder.procedure_templates;
        const template = &templates.templates.items[@backingInt(implicit.template)];
        const bound_call = for (templates.templateLiteralRequirements(template)) |requirement| {
            if (requirement.site.kind == .bound_call) break requirement;
        } else continue;
        try scan.refused_methods.append(gpa, .{ .key = entry.key, .rejection = .{
            .kind = .bound_call_in_implicit_method,
            .region = boundCallRegion(reifier, holder, target, implicit, bound_call),
            .module = reifier.rejectionModule(),
            .detail = method.text(),
        } });
    }
}

/// Where a descriptor method that needs a generic bound call's input
/// binding is refused (Q17): the call in the method's body that reaches the
/// bound call, the bound call where the body holds it, else the method's
/// body, or for a target of another module the method's binding.
fn boundCallRegion(reifier: *Reifier, holder: *Reifier, target: static_dispatch.MethodTarget, implicit: ImplicitTarget, requirement: checked.LiteralRequirement) base.Region {
    if (holder != reifier) {
        const alias = target.alias orelse
            invariant("a method bound to another module's procedure has no alias binding");
        return switch (alias.binding) {
            .top_level => |pattern| reifier.env.store.getPatternRegion(pattern),
            .local => |local| reifier.env.store.getExprRegion(local.lookup),
        };
    }
    return switch (requirement.edge) {
        .use => |use| reifier.env.store.getExprRegion(use),
        .literal => reifier.env.store.getExprRegion(@fromBackingInt(requirement.site.node)),
        .node, .requirement, .derivation_call => reifier.bodies.expr(implicit.body).source_region,
    };
}

fn templateIdLessThan(_: void, a: canonical.CheckedProcedureTemplateId, b: canonical.CheckedProcedureTemplateId) bool {
    return @backingInt(a) < @backingInt(b);
}

/// The recipes of a module's instance sites (D1), and the pools they span.
const RecipeBuilder = struct {
    gpa: Allocator,
    recipes: std.ArrayList(Inventories.Recipe) = .empty,
    scheme_vars: std.ArrayList(CheckedTypeId) = .empty,
    args: std.ArrayList(ExprId) = .empty,
    modules: std.ArrayList(checked.CheckedModuleArtifactKey) = .empty,

    fn deinit(self: *RecipeBuilder) void {
        self.recipes.deinit(self.gpa);
        self.scheme_vars.deinit(self.gpa);
        self.args.deinit(self.gpa);
        self.modules.deinit(self.gpa);
    }

    /// The `modules` index of `reader`'s module, or `none` for the site's
    /// own module.
    fn moduleOf(self: *RecipeBuilder, site: *Reifier, reader: *Reifier) Allocator.Error!u32 {
        if (reader == site) return Inventories.none;
        for (self.modules.items, 0..) |key, index| {
            if (std.meta.eql(key.bytes, reader.artifact.bytes)) return @intCast(index);
        }
        try self.modules.append(self.gpa, reader.artifact);
        return @intCast(self.modules.items.len - 1);
    }

    fn schemeSpan(self: *RecipeBuilder, scheme: ?Reifier.Scheme) Allocator.Error!struct { vars: code_analyses.Span, root: ?CheckedTypeId } {
        const known = scheme orelse return .{ .vars = .{}, .root = null };
        const start: u32 = @intCast(self.scheme_vars.items.len);
        try self.scheme_vars.appendSlice(self.gpa, known.vars);
        return .{ .vars = .{ .start = start, .len = @intCast(known.vars.len) }, .root = known.root };
    }

    /// Resolve one instance site to what a closing use's walk reads, or the
    /// reason no closing use can describe it.
    fn resolve(
        self: *RecipeBuilder,
        walk: *Walk,
        reifier: *Reifier,
        info: SiteInfo,
        site_expr: ExprId,
        region: base.Region,
        call_args: *std.ArrayList(ExprId),
    ) Allocator.Error!union(enum) { recipe: u32, rejected: Rejection } {
        const site = info.record;
        var recipe: Inventories.Recipe = .{
            .kind = .inline_lambda,
            .view = site.view,
            .fn_ty = info.fn_ty,
            .region = region,
            .root_module = Inventories.none,
            .root_body = site_expr,
            .scheme_vars = .{},
            .scheme_root = null,
            .in_block = true,
            .use = null,
            .translator = translatorCall(reifier, site),
            .args = .{},
        };
        switch (site.kind) {
            .inline_lambda => {},
            .value => recipe.kind = .value,
            .named_function => {
                walk.rejection = null;
                const root = switch (try namedRoot(walk, reifier, site.node_idx, region)) {
                    .root => |root| root,
                    .rejected => |rejection| return .{ .rejected = rejection },
                };
                const scheme = try self.schemeSpan(root.scheme);
                recipe.kind = .named_function;
                recipe.root_module = try self.moduleOf(reifier, root.reader);
                recipe.root_body = root.body;
                recipe.scheme_vars = scheme.vars;
                recipe.scheme_root = scheme.root;
                recipe.in_block = root.in_block;
                recipe.use = root.use;
            },
            .template_call => {
                const call = try templateCall(self.gpa, reifier, site.node_idx, call_args, walk.foreign) orelse
                    return .{ .rejected = unreachableDefinition(reifier, region, "a template this module cannot read").rejected };
                const root_reader, const body, const template = switch (call.template) {
                    .here => |definition| .{ reifier, definition.body, definition.template },
                    .away => |definition| .{ try walk.reader(definition.module), definition.body, definition.template },
                };
                const scheme = try self.schemeSpan(root_reader.templateScheme(template));
                const args_start: u32 = @intCast(self.args.items.len);
                try self.args.appendSlice(self.gpa, call.args);
                recipe.kind = .template_call;
                recipe.root_module = try self.moduleOf(reifier, root_reader);
                recipe.root_body = body;
                recipe.scheme_vars = scheme.vars;
                recipe.scheme_root = scheme.root;
                recipe.in_block = false;
                recipe.use = call.callee;
                recipe.args = .{ .start = args_start, .len = @intCast(call.args.len) };
            },
            .template, .template_callee => unreachable, // the site map holds walked sites only
        }
        try self.recipes.append(self.gpa, recipe);
        return .{ .recipe = @intCast(self.recipes.items.len - 1) };
    }
};

/// The entry template the evaluation of the constant with body `body` runs,
/// or null for a constant evaluation already stored.
fn constantEntryTemplate(reifier: *const Reifier, body: checked.CheckedConstBodyRef) ?canonical.CheckedProcedureTemplateId {
    for (reifier.const_templates.templates.items) |template| switch (template.state) {
        .eval_template => |eval| if (eval.body == body) {
            if (!std.meta.eql(eval.entry_template.artifact.bytes, reifier.artifact.bytes)) invariant("a constant's entry template is in another module");
            return eval.entry_template.template;
        },
        .stored_const, .reserved, .unimplemented => {},
    };
    return null;
}

/// Whether a module this module depends on holds an inventory: an import,
/// or an import of an import, to any depth. A use reaches a template of a
/// module it does not import through an exact alias another module exports
/// (`reachedAway`) or a method of a nominal another module declares
/// (`methodDefinition`), and each such module is a dependency of a module
/// on the way. An importer is never visited, so no slot reads its own.
fn importsHoldInventories(reifier: *Reifier) Allocator.Error!bool {
    const gpa = reifier.gpa;
    var seen: std.AutoHashMapUnmanaged([32]u8, void) = .empty;
    defer seen.deinit(gpa);
    var work = std.ArrayList(ForeignModule).empty;
    defer work.deinit(gpa);
    try pushImports(gpa, reifier.env, reifier.lookup, &seen, &work);
    while (work.pop()) |module| {
        if ((try module.sources.bodies.codeInventories(module)).inventories.len != 0) return true;
        try pushImports(gpa, module.env(), module.lookup, &seen, &work);
    }
    return false;
}

/// Queue each module an import of `env` resolved to that is not yet seen.
fn pushImports(
    gpa: Allocator,
    env: *const ModuleEnv,
    lookup: ForeignLookup,
    seen: *std.AutoHashMapUnmanaged([32]u8, void),
    work: *std.ArrayList(ForeignModule),
) Allocator.Error!void {
    for (0..env.imports.imports.items.items.len) |raw| {
        const module = lookup.findImportModule(@fromBackingInt(@as(u32, @intCast(raw)))) orelse continue;
        if ((try seen.getOrPut(gpa, module.sources.artifact.bytes)).found_existing) continue;
        try work.append(gpa, module);
    }
}

/// The scan of a top-level binding that is no procedure body, at the
/// variables of its type `ty` (Q16).
fn scanBinding(
    gpa: Allocator,
    reifier: *Reifier,
    site_map: *const collections.DenseMapUnmanaged(ExprId, SiteInfo),
    identity_map: *const IdentityMap,
    out: *std.ArrayList(Occurrence),
    implicit: *ImplicitScan,
    edges: *EdgeScan,
    ty: CheckedTypeId,
    body: ExprId,
) Allocator.Error!void {
    var vars: Reifier.RowVars = .empty;
    defer vars.deinit(gpa);
    try reifier.collectVars(ty, &vars);
    var scan = OccurrenceScan{ .r = reifier, .sites = site_map, .identities = identity_map, .template = null, .template_vars = &vars, .out = out, .implicit = implicit, .edges = edges };
    defer scan.local_vars.deinit(gpa);
    try scan.expr(body, null);
}

/// Keep the first record of each expression: a lambda a constant holds may
/// also be a body of its own.
fn dedupeOccurrences(gpa: Allocator, occurrences: *std.ArrayList(Occurrence)) Allocator.Error!void {
    var seen: collections.DenseMapUnmanaged(ExprId, void) = .empty;
    defer seen.deinit(gpa);
    var kept: usize = 0;
    for (occurrences.items) |occurrence| {
        if ((try seen.getOrPut(gpa, occurrence.expr)).found_existing) continue;
        occurrences.items[kept] = occurrence;
        kept += 1;
    }
    occurrences.shrinkRetainingCapacity(kept);
}

/// Keep the first record of each edge: a lambda a constant holds may also
/// be a body of its own, and one evidence node can stand in the evidence of
/// more than one use.
fn dedupeEdges(gpa: Allocator, edges: *std.ArrayList(EdgeOccurrence)) Allocator.Error!void {
    var seen: std.AutoHashMapUnmanaged(CodeEdgeKey, u32) = .empty;
    defer seen.deinit(gpa);
    var kept: usize = 0;
    for (edges.items) |occurrence| {
        const entry = try seen.getOrPut(gpa, CodeEdgeKey.of(occurrence.edge));
        if (entry.found_existing) {
            // An edge's types mention the variables of one scheme at most,
            // so an edge at a template's variables stands in that one
            // template's body.
            const first = edges.items[entry.value_ptr.*];
            std.debug.assert(!occurrence.template_vars or (first.template_vars and std.meta.eql(first.template, occurrence.template)));
            continue;
        }
        entry.value_ptr.* = @intCast(kept);
        edges.items[kept] = occurrence;
        kept += 1;
    }
    edges.shrinkRetainingCapacity(kept);
}

/// An edge that the evidence of a use reaches (design.md "Code Instance
/// Tables"): an evidence node other than a method call's own target, or a
/// call of a generated codec contract. A template the edge selects is
/// described at the edge, as at a use: a closing edge has a table, and an
/// edge at the variables of the template whose body holds it is a forward
/// entry of that template's inventory.
const EdgeOccurrence = struct {
    edge: CodeEdge,
    /// The use whose evidence holds the edge, where a report points.
    at: ExprId,
    /// The expression a refused edge makes a runtime error, as for its use.
    poison: ExprId,
    /// The statement a refused edge makes a runtime error in place of
    /// `poison`: a `for` statement whose iterator's evidence holds the edge.
    statement: ?StatementId = null,
    template: ?canonical.CheckedProcedureTemplateId,
    /// Whether the edge's types mention a quantified variable of `template`.
    template_vars: bool,
    /// Whether they mention a quantified variable of a lambda a block
    /// generalized (Q5).
    local_vars: bool,
};

/// The types an edge to `node`'s target fixes: the substitution of a
/// procedure's scheme, or the callable a method bound to a computed callable
/// is related to, which fixes its entry wrapper (`computedMethodCallee`).
/// `callable` holds the latter. Null for a method declared in a function
/// body, which is called through its function value.
fn nodeTypes(plans: *const static_dispatch.StaticDispatchPlanTable, node: static_dispatch.EvidenceNode, callable: *[1]CheckedTypeId) ?[]const CheckedTypeId {
    return switch (node.target.kind) {
        .procedure => plans.targetSubstitution(node),
        .callable_binding => switch (node.instantiation) {
            .callable, .alias, .derived_from_callable => |callable_ty| blk: {
                callable[0] = callable_ty;
                break :blk callable;
            },
            .monomorphic => &.{},
        },
        .local_proc, .structural => null,
    };
}

/// The edges of the uses of a module's bodies, read through the walk the
/// literal requirement computation reads them with
/// (`static_dispatch.EvidenceEdgeWalk`), which calls `evidenceNode` and
/// `contractCall` here.
const EdgeScan = struct {
    walk: static_dispatch.EvidenceEdgeWalk,
    out: *std.ArrayList(EdgeOccurrence),
    /// The body scan the walk is in, and the use whose evidence it reads.
    body: *OccurrenceScan = undefined,
    at: ExprId = undefined,
    poison: ExprId = undefined,
    statement: ?StatementId = null,

    pub fn evidenceNode(e: *EdgeScan, id: static_dispatch.EvidenceNodeId, node: static_dispatch.EvidenceNode) Allocator.Error!void {
        var callable: [1]CheckedTypeId = undefined;
        const types = nodeTypes(e.body.r.plans, node, &callable) orelse return;
        try e.record(.{ .node = id }, types, &.{});
    }

    /// The walk passes the call's callable type, which the edge's key and
    /// types do not need.
    pub fn contractCall(e: *EdgeScan, derivation: static_dispatch.GeneratedCodecDerivationId, _: CheckedTypeId, node_id: static_dispatch.EvidenceNodeId) Allocator.Error!void {
        const plans = e.body.r.plans;
        var callable: [1]CheckedTypeId = undefined;
        const types = nodeTypes(plans, plans.evidenceNode(node_id), &callable) orelse return;
        const contract = plans.generated_codec_derivations[@backingInt(derivation)];
        try e.record(.{ .derivation_call = .{ .derivation = derivation, .node = node_id } }, types, contract.renamedVarsSlice(plans));
    }

    /// Record `edge`, whose types are `subst`. A variable of `renamed` (a
    /// contract's renamed copy) stands for the type of the relation it
    /// renamed, so it mentions what that type mentions.
    fn record(e: *EdgeScan, edge: CodeEdge, subst: []const CheckedTypeId, renamed: []const static_dispatch.GeneratedCodecRenamedVar) Allocator.Error!void {
        const s = e.body;
        const gpa = s.r.gpa;
        var through_template: Reifier.RowVars = .empty;
        defer through_template.deinit(gpa);
        var through_local: Reifier.RowVars = .empty;
        defer through_local.deinit(gpa);
        for (renamed) |pair| {
            const found = try s.mentions(pair.original);
            if (found.template) try through_template.put(gpa, pair.copy, {});
            if (found.local) try through_local.put(gpa, pair.copy, {});
        }
        var template_vars = false;
        var local_vars = false;
        for (subst) |ty| {
            // A substitution entry that fixes a kind variable is no type.
            if (s.r.types.payload(ty) == .field_kind) continue;
            const found = try s.mentions(ty);
            template_vars = template_vars or found.template or try s.r.mentionsAny(ty, &through_template);
            local_vars = local_vars or found.local or try s.r.mentionsAny(ty, &through_local);
        }
        // Checking validates a codec relation whose type has a generalized
        // variable at each use (`activateSchemeDeferredCodecConstraints`), so
        // a contract derives a relation at closed types or at the template's
        // own fresh copies, never at a holder's variables.
        std.debug.assert(!(edge == .derivation_call and template_vars));
        try e.out.append(gpa, .{ .edge = edge, .at = e.at, .poison = e.poison, .statement = e.statement, .template = s.template, .template_vars = template_vars, .local_vars = local_vars });
    }
};

/// One body's walk for D1: each site it holds, and each use of a procedure
/// it makes, with whether each one's type mentions a variable the body's
/// template or a lambda a block generalized quantifies over. A site is not
/// entered: what its lambda calls is described, not run.
const OccurrenceScan = struct {
    r: *Reifier,
    sites: *const collections.DenseMapUnmanaged(ExprId, SiteInfo),
    identities: *const IdentityMap,
    template: ?canonical.CheckedProcedureTemplateId,
    template_vars: *const Reifier.RowVars,
    /// The quantified variables of every generalized lambda the walk is
    /// inside.
    local_vars: Reifier.RowVars = .empty,
    out: *std.ArrayList(Occurrence),
    /// The scan of the type occurrences of the descriptor methods (Q17).
    implicit: *ImplicitScan,
    /// The scan of the edges of the uses' evidence.
    edges: *EdgeScan,

    /// The edge scan, in this body at the use `at`.
    fn edgesAt(s: *OccurrenceScan, at: ExprId, poison: ExprId) *EdgeScan {
        s.edges.body = s;
        s.edges.at = at;
        s.edges.poison = poison;
        s.edges.statement = null;
        return s.edges;
    }

    /// The edges of the dispatches a `Code.Binds` site runs where the
    /// program binds its inputs: `fmt.default()`, and `T.encoder_for` of
    /// each value it captures (design.md "Code Reification"). Each target,
    /// and the evidence each supplies, is an edge, keyed by its node, since
    /// no use names these dispatches.
    fn boundCaptureEdges(s: *OccurrenceScan, site: ExprId) Allocator.Error!void {
        const r = s.r;
        const encodings = r.env.boundCaptureEncodingsForSite(@backingInt(site));
        if (encodings.len == 0) return;
        const edges = s.edgesAt(site, site);
        try s.planEdges(edges, r.plans.boundCaptureDefaultPlan(site) orelse invariant("a bound capture site has no default plan"));
        for (encodings) |encoding| {
            try s.planEdges(edges, r.plans.boundCaptureEncoderPlan(@fromBackingInt(encoding.read_expr)) orelse invariant("a bound capture read has no encoder plan"));
        }
        try edges.walk.nodes(edges, null);
    }

    /// The edges of a dispatch plan no use names: its target's node, and
    /// what that node's evidence reaches, or the calls of its contract.
    fn planEdges(s: *OccurrenceScan, edges: *EdgeScan, plan_id: static_dispatch.StaticDispatchPlanId) Allocator.Error!void {
        const plan = s.r.plans.plans[@backingInt(plan_id)];
        switch (plan.resolution) {
            .direct_closed, .direct_parametric => |direct| try edges.walk.stack.append(edges.walk.allocator, direct.evidence),
            .structural => if (plan.generated_codec_derivation) |derivation| try edges.walk.derivation(edges, derivation),
            .direct_pending, .evidence_dependent, .checked_error, .@"unreachable" => {},
        }
    }

    fn mentions(s: *OccurrenceScan, ty: CheckedTypeId) Allocator.Error!struct { template: bool, local: bool } {
        return .{
            .template = try s.r.mentionsAny(ty, s.template_vars),
            .local = try s.r.mentionsAny(ty, &s.local_vars),
        };
    }

    fn record(s: *OccurrenceScan, kind: @FieldType(Occurrence, "kind"), id: ExprId, poison: ExprId, types: []const CheckedTypeId) Allocator.Error!void {
        var template_vars = false;
        var local_vars = false;
        for (types) |ty| {
            // A substitution entry that fixes a kind variable is no type.
            if (s.r.types.payload(ty) == .field_kind) continue;
            // A use's types are types the program runs at.
            if (kind == .use) try s.implicit.occurrences(s, id, ty);
            const found = try s.mentions(ty);
            template_vars = template_vars or found.template;
            local_vars = local_vars or found.local;
        }
        try s.out.append(s.r.gpa, .{
            .kind = kind,
            .expr = id,
            .poison = poison,
            .template = s.template,
            .template_vars = template_vars,
            .local_vars = local_vars,
            .edge = .{ .use = id },
        });
    }

    fn exprs(s: *OccurrenceScan, ids: []const ExprId) Allocator.Error!void {
        for (ids) |id| try s.expr(id, null);
    }

    /// `call` is the call `id` is the callee of, or null.
    fn expr(s: *OccurrenceScan, id: ExprId, call: ?ExprId) Allocator.Error!void {
        const r = s.r;
        if (s.sites.get(id)) |info| {
            try s.boundCaptureEdges(id);
            // A template's lambda and the name a template call calls stand
            // for descriptions built elsewhere, and run nothing here.
            switch (info.record.kind) {
                .named_function, .inline_lambda, .template_call => try s.record(.site, id, id, &.{info.fn_ty}),
                // A value a call binds also runs here: the program computes
                // it where the call binds its slot.
                .value => {
                    try s.record(.site, id, id, &.{info.fn_ty});
                    if (info.record.bound_call != CodeSiteRecord.no_bound_call) try s.exprData(id, call, r.bodies.openingValueSite(id).expr(id).data);
                },
                .template, .template_callee => {},
            }
            return;
        }
        if (s.identities.get(id)) |info| {
            try s.record(.identity, id, id, &.{r.bodies.expr(info.arg).ty});
            return;
        }
        const checked_expr = r.bodies.expr(id);
        try s.implicit.occurrences(s, id, checked_expr.ty);
        // The evidence an instantiation of a scheme supplies: a lookup's, or
        // a generalized local function's construction's.
        if (r.plans.siteEvidence(id)) |evidence| {
            const edges = s.edgesAt(id, call orelse id);
            try edges.walk.entries(edges, evidence);
            try edges.walk.nodes(edges, null);
        }
        try s.exprData(id, call, checked_expr.data);
    }

    /// Scan the expression `id` of shape `data`.
    fn exprData(s: *OccurrenceScan, id: ExprId, call: ?ExprId, data: checked_bodies.ExprData) Allocator.Error!void {
        const r = s.r;
        switch (data) {
            .lookup_local, .lookup_external => {
                const resolved = r.lookupResolved(id) orelse return;
                const ty = switch (r.value_refs.callableTarget(resolved).ref) {
                    .top_level_proc, .imported_proc, .promoted_top_level_proc => |use| use.source_fn_ty_payload,
                    // A constant evaluation computes at each type a use
                    // fixes (Q16).
                    .top_level_const, .imported_const => |use| use.requested_source_ty_payload,
                    .hosted_proc, .local_proc, .local_param, .local_value, .local_mutable_version, .pattern_binder, .selected_hoisted_const, .platform_required_declaration, .platform_required_checked_error, .platform_required_const, .platform_required_proc => return,
                };
                var types = std.ArrayList(CheckedTypeId).empty;
                defer types.deinit(r.gpa);
                if (ty) |fixed| try types.append(r.gpa, fixed);
                if (r.plans.siteSubstitution(id)) |copied| try types.appendSlice(r.gpa, copied);
                try s.record(.use, id, call orelse id, types.items);
            },
            // `a == b` on a written `is_eq`, and `T.method(..)`, are static
            // dispatches as a method call is.
            .dispatch_call, .method_eq, .type_dispatch_call => {
                const plan_ref = r.bodies.dispatchPlan(@backingInt(id)) orelse return;
                const dispatch = r.plans.plans[@backingInt(plan_ref)];
                const edges = s.edgesAt(id, id);
                switch (dispatch.resolution) {
                    .direct_closed, .direct_parametric => |direct| {
                        const node = r.plans.evidenceNode(direct.evidence);
                        var callable: [1]CheckedTypeId = undefined;
                        if (nodeTypes(r.plans, node, &callable)) |types| {
                            // The call is a use of its own target, whose
                            // table its node keys; the evidence the call
                            // supplies the target holds edges.
                            try s.record(.use, id, id, types);
                            s.out.items[s.out.items.len - 1].edge = .{ .node = direct.evidence };
                        }
                        try edges.walk.nested(edges, node);
                    },
                    // A written `encoder_for` or `parser_for` call's
                    // contract (design.md "Literal Arguments").
                    .structural => if (dispatch.generated_codec_derivation) |derivation| try edges.walk.derivation(edges, derivation),
                    .direct_pending, .evidence_dependent, .checked_error, .@"unreachable" => {},
                }
                try edges.walk.nodes(edges, null);
                try s.dispatchOperands(plan_ref);
            },
            .lambda => |lambda| try s.scoped(id, lambda.body),
            .closure => |closure| try s.scoped(id, closure.lambda),
            .str, .list, .tuple => |items| try s.exprs(items),
            .match_ => |m| {
                try s.expr(m.cond, null);
                for (m.branches) |branch_idx| {
                    const branch = r.bodies.matchBranch(branch_idx);
                    if (branch.guard) |guard| try s.expr(guard, null);
                    try s.expr(branch.value, null);
                }
            },
            .if_ => |i| {
                for (i.branches) |branch_idx| {
                    const branch = r.bodies.ifBranch(branch_idx);
                    try s.expr(branch.cond, null);
                    try s.expr(branch.body, null);
                }
                try s.expr(i.final_else, null);
            },
            .call => |c| {
                try s.expr(c.func, id);
                try s.exprs(c.args);
            },
            .record => |rec| {
                if (rec.ext) |ext| try s.expr(ext, null);
                for (rec.fields) |field| try s.expr(r.bodies.recordFieldValue(field), null);
            },
            .block => |block| {
                for (block.statements) |stmt| try s.statement(stmt);
                try s.expr(block.final_expr, null);
            },
            .tag => |t| try s.exprs(t.args),
            .nominal => |n| try s.expr(n.backing_expr, null),
            .binop => |op| {
                try s.expr(op.lhs, null);
                try s.expr(op.rhs, null);
            },
            .unary_minus, .dbg, .expect => |operand| try s.expr(operand, null),
            .field_access => |access| try s.expr(access.receiver, null),
            .tuple_access => |access| try s.expr(access.tuple, null),
            .interpolation => |interpolation| {
                for (0..interpolation.segmentCount()) |k| try s.expr(interpolation.segment(k), null);
                for (0..interpolation.valueCount()) |k| try s.expr(interpolation.value(k), null);
            },
            .structural_eq => |eq| {
                try s.expr(eq.lhs, null);
                try s.expr(eq.rhs, null);
            },
            .structural_hash => |hash| {
                try s.expr(hash.value, null);
                try s.expr(hash.hasher, null);
            },
            .expect_err => |e| try s.expr(e.expr, null),
            .return_ => |returned| try s.expr(returned.expr, null),
            .for_ => |loop| {
                try s.iterUse(r.bodies.iteratorForPlan(@backingInt(id)), loop.body, loop.expr, id, null);
                try s.expr(loop.expr, null);
                try s.expr(loop.body, null);
            },
            .run_low_level => |run| try s.exprs(run.args),
            // A retired expression still evaluates the operands it records,
            // up to and including the erroneous one, so a use among them is
            // lowered and needs its table like any other.
            .runtime_error => |runtime_error| try s.exprs(runtime_error.evaluated),
            .numeral,
            .code_site,
            .str_segment,
            .bytes_literal,
            .lookup_required,
            .empty_list,
            .empty_record,
            .zero_argument_tag,
            .crash,
            .ellipsis,
            .anno_only,
            .hosted_lambda,
            .break_,
            => {},
        }
    }

    /// A lambda's body, inside the scope of the lambda when a block
    /// generalized it.
    fn scoped(s: *OccurrenceScan, lambda: ExprId, inner: ExprId) Allocator.Error!void {
        const r = s.r;
        var added = std.ArrayList(CheckedTypeId).empty;
        defer added.deinit(r.gpa);
        for (r.procedure_templates.dispatch_scopes) |*scope| {
            if (scope.checked_expr != lambda) continue;
            for (r.procedure_templates.scopeSchemeVars(scope)) |scheme_var| {
                if ((try s.local_vars.getOrPut(r.gpa, scheme_var)).found_existing) continue;
                try added.append(r.gpa, scheme_var);
            }
        }
        defer for (added.items) |scheme_var| {
            _ = s.local_vars.remove(scheme_var);
        };
        try s.expr(inner, null);
    }

    fn dispatchOperands(s: *OccurrenceScan, plan_id: static_dispatch.StaticDispatchPlanId) Allocator.Error!void {
        const p = s.r.plans.plans[@backingInt(plan_id)];
        for (p.argsSlice(s.r.plans)) |operand| switch (operand) {
            .checked_expr, .generated_interpolation_segments => |child| try s.expr(child, null),
            .generated_numeral, .generated_quote, .literal_pattern_value, .literal_pattern_conversion, .bound_capture_default => {},
        };
    }

    /// A `for` loop's `iter` call, a direct static dispatch, keyed by the
    /// loop's body. A refused use poisons the loop expression, or, for a
    /// statement, the statement.
    fn iterUse(s: *OccurrenceScan, plan_id: ?static_dispatch.IteratorForPlanId, body: ExprId, iterable: ExprId, poison: ExprId, statement_id: ?StatementId) Allocator.Error!void {
        const plan = s.r.plans.iterator_for_plans[@backingInt(plan_id orelse return)];
        const direct = switch (plan.iter.resolution) {
            .direct_closed, .direct_parametric => |direct| direct,
            .direct_pending, .evidence_dependent, .structural, .checked_error, .@"unreachable" => return,
        };
        const node = s.r.plans.evidenceNode(direct.evidence);
        // The evidence the loop's `iter` and `next` calls supply their
        // targets holds edges, as a dispatch's does.
        const edges = s.edgesAt(iterable, poison);
        edges.statement = statement_id;
        try edges.walk.nested(edges, node);
        // The `next` call's own target is an edge too, as a dispatch's is.
        const next_node: ?static_dispatch.EvidenceNodeId = switch (plan.next.resolution) {
            .direct_closed, .direct_parametric => |next| next.evidence,
            .direct_pending, .evidence_dependent, .structural, .checked_error, .@"unreachable" => null,
        };
        try edges.walk.nodes(edges, next_node);
        var callable: [1]CheckedTypeId = undefined;
        try s.record(.use, body, poison, nodeTypes(s.r.plans, node, &callable) orelse return);
        s.out.items[s.out.items.len - 1].statement = statement_id;
        s.out.items[s.out.items.len - 1].shown = iterable;
    }

    fn statement(s: *OccurrenceScan, id: StatementId) Allocator.Error!void {
        switch (s.r.bodies.statement(id).data) {
            .decl => |decl| try s.expr(decl.expr, null),
            .var_ => |decl| try s.expr(decl.expr, null),
            .reassign => |assignment| try s.expr(assignment.expr, null),
            .dbg, .expr, .expect => |e| try s.expr(e, null),
            .for_ => |loop| {
                try s.iterUse(s.r.bodies.iteratorForPlan(@backingInt(id)), loop.body, loop.expr, loop.body, id);
                try s.expr(loop.expr, null);
                try s.expr(loop.body, null);
            },
            .while_, .infinite_loop, .breakable_loop => |loop| {
                try s.expr(loop.cond, null);
                try s.expr(loop.body, null);
            },
            .return_ => |returned| try s.expr(returned.expr, null),
            // A promoted function's body is its own procedure, which runs
            // nothing here.
            .promoted_proc,
            .rejected_method_decl,
            .var_uninitialized,
            .crash,
            .break_,
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

/// One type occurrence, in a body, of a nominal whose descriptor method
/// (Q17) has a target that can hold an inventory: the method's table at
/// the owner type is described where the type occurs (design.md "Code
/// Instance Tables").
const ImplicitOccurrence = struct {
    method: DescriptorMethod,
    /// The owner type, a `ModuleScan.terms` index.
    owner: u32,
    /// The expression whose type, or whose use's substitution, holds it.
    expr: ExprId,
    /// The template whose body holds it, or null for a body of no template.
    template: ?canonical.CheckedProcedureTemplateId,
    /// Whether the owner type mentions a quantified variable of `template`.
    template_vars: bool,
    /// Whether it mentions a quantified variable of a lambda a block
    /// generalized (Q5).
    local_vars: bool,
    /// The template the method runs.
    target: ImplicitTarget,
};

/// The template a descriptor method runs: a procedure, or the entry
/// wrapper of a method bound to a computed callable.
const ImplicitTarget = struct {
    artifact: [32]u8,
    template: canonical.CheckedProcedureTemplateId,
    /// The body the template runs: the procedure's, or the computed
    /// callable's binding's.
    body: ExprId,
    /// Whether it is a computed callable's entry wrapper, which returns the
    /// method's function.
    computed: bool,
};

const DescriptorMethod = code_analyses.DescriptorMethod;
const TypeTerms = code_analyses.TypeTerms;

/// The descriptor methods, in `DescriptorMethod` order.
const descriptor_methods = std.enums.values(DescriptorMethod);

/// The terms of one module's type occurrences (`TypeTerms`), each kept once.
const TermPool = struct {
    terms: std.ArrayList(TypeTerms.Term) = .empty,
    bindings: std.ArrayList(TypeTerms.Binding) = .empty,
    /// The type and the bindings of each term, as bytes, to its index.
    index: std.StringHashMapUnmanaged(u32) = .empty,

    fn deinit(self: *TermPool, gpa: Allocator) void {
        self.terms.deinit(gpa);
        self.bindings.deinit(gpa);
        var keys = self.index.keyIterator();
        while (keys.next()) |key| gpa.free(key.*);
        self.index.deinit(gpa);
    }

    /// The term of `ty` with `bindings`, made or shared.
    fn intern(self: *TermPool, gpa: Allocator, ty: CheckedTypeId, bindings: []const TypeTerms.Binding) Allocator.Error!u32 {
        var key = std.ArrayList(u8).empty;
        defer key.deinit(gpa);
        try key.appendSlice(gpa, std.mem.asBytes(&@as(u32, @backingInt(ty))));
        for (bindings) |binding| {
            try key.appendSlice(gpa, std.mem.asBytes(&@as(u32, @backingInt(binding.variable))));
            try key.appendSlice(gpa, std.mem.asBytes(&binding.term));
        }
        if (self.index.get(key.items)) |existing| return existing;
        const start: u32 = @intCast(self.bindings.items.len);
        try self.bindings.appendSlice(gpa, bindings);
        const index: u32 = @intCast(self.terms.items.len);
        try self.terms.append(gpa, .{ .ty = ty, .bindings = .{ .start = start, .len = @intCast(bindings.len) } });
        const owned = try gpa.dupe(u8, key.items);
        errdefer gpa.free(owned);
        try self.index.put(gpa, owned, index);
        return index;
    }

    fn termBindings(self: *const TermPool, term: u32) []const TypeTerms.Binding {
        const span = self.terms.items[term].bindings;
        return self.bindings.items[span.start..][0..span.len];
    }

    /// The pools as a `TypeTerms` the caller owns.
    fn toOwned(self: *const TermPool, gpa: Allocator) Allocator.Error!TypeTerms {
        const terms = try gpa.dupe(TypeTerms.Term, self.terms.items);
        errdefer gpa.free(terms);
        return .{ .terms = terms, .bindings = try gpa.dupe(TypeTerms.Binding, self.bindings.items) };
    }
};

/// The term `id` is, read inside a term with `bindings`: a variable the
/// bindings fix is the term it is bound to.
fn boundTerm(pool: *TermPool, gpa: Allocator, types: checked.CheckedTypeStoreView, id: CheckedTypeId, bindings: []const TypeTerms.Binding) Allocator.Error!u32 {
    switch (types.payload(id)) {
        .flex, .rigid => for (bindings) |binding| {
            if (binding.variable == id) return binding.term;
        },
        .field_kind, .pending, .err, .alias, .record, .tuple, .nominal, .function, .empty_record, .tag_union, .empty_tag_union => {},
    }
    return pool.intern(gpa, id, bindings);
}

/// The scan of the type occurrences of the descriptor methods (Q17) in one
/// module's bodies. The type of each expression and each use's
/// substitution is read, and closed over its components, its nominals'
/// arguments and its nominals' backings: a derived method of a structure
/// calls the method of each nominal inside it. A recursive type closes,
/// since a term is visited once per body.
const ImplicitScan = struct {
    r: *Reifier,
    terms: *TermPool,
    out: *std.ArrayList(ImplicitOccurrence),
    /// This module's refused methods (`refusedMethods`).
    own_refused: *const std.ArrayList(code_analyses.CodeInventories.RefusedMethod),
    /// The terms the current body visited.
    visited: collections.DenseMapUnmanaged(u32, void) = .empty,
    /// The body whose terms `visited` holds.
    body_template: ?canonical.CheckedProcedureTemplateId = null,
    body_vars: ?*const Reifier.RowVars = null,
    /// Each occurrence recorded: the template (or `none`), the method and
    /// the owner term.
    recorded: std.AutoHashMapUnmanaged(RecordedKey, void) = .empty,
    /// The descriptor method targets of each nominal met, by its
    /// declaring module's identity and declaration.
    nominals: std.AutoHashMapUnmanaged(struct { module: [32]u8, decl: u32 }, [descriptor_methods.len]?ImplicitTarget) = .empty,
    work: std.ArrayList(u32) = .empty,

    const RecordedKey = struct { template: u32, method: DescriptorMethod, owner: u32 };

    fn deinit(self: *ImplicitScan) void {
        const gpa = self.r.gpa;
        self.visited.deinit(gpa);
        self.recorded.deinit(gpa);
        self.nominals.deinit(gpa);
        self.work.deinit(gpa);
    }

    /// Record the descriptor method occurrences `ty`, a type of the
    /// expression `expr` of the body `s` walks, holds.
    fn occurrences(self: *ImplicitScan, s: *OccurrenceScan, expr: ExprId, ty: CheckedTypeId) Allocator.Error!void {
        const r = self.r;
        const gpa = r.gpa;
        // A term mentions the variables of the body it is read in, so the
        // terms are visited again in each body.
        if (self.body_template != s.template or self.body_vars != s.template_vars) {
            self.visited.clearRetainingCapacity();
            self.body_template = s.template;
            self.body_vars = s.template_vars;
        }
        self.work.clearRetainingCapacity();
        try self.work.append(gpa, try self.terms.intern(gpa, ty, &.{}));
        while (self.work.pop()) |term_index| {
            if ((try self.visited.getOrPut(gpa, term_index)).found_existing) continue;
            const term = self.terms.terms.items[term_index];
            const bindings = try gpa.dupe(TypeTerms.Binding, self.terms.termBindings(term_index));
            defer gpa.free(bindings);
            switch (r.types.payload(term.ty)) {
                .field_kind => invariant("a field kind is a substitution entry, never part of a type"),
                .flex, .rigid => for (bindings) |binding| {
                    if (binding.variable == term.ty) try self.work.append(gpa, binding.term);
                },
                .alias => |alias| try self.child(alias.backing, bindings),
                .function => |fn_ty| {
                    for (fn_ty.args) |arg| try self.child(arg, bindings);
                    try self.child(fn_ty.ret, bindings);
                },
                .tuple => |parts| for (parts) |part| try self.child(part, bindings),
                .record => |record| {
                    var fields = record.fields.iterator();
                    while (fields.next()) |field| try self.child(field.ty, bindings);
                    try self.child(record.ext, bindings);
                },
                .tag_union => |union_ty| {
                    var tags = union_ty.tags.iterator();
                    while (tags.next()) |variant| for (variant.args) |arg| try self.child(arg, bindings);
                    try self.child(union_ty.ext, bindings);
                },
                .nominal => |nominal| {
                    try self.nominalOccurrence(s, expr, nominal, term_index);
                    const backing = r.types.nominalBackingTemplateForPayload(nominal);
                    if (backing == null or nominal.args.len == 0) {
                        for (nominal.args) |arg| try self.child(arg, bindings);
                        if (backing) |found| try self.work.append(gpa, try self.terms.intern(gpa, found, &.{}));
                        continue;
                    }
                    // The backing reads the declaration's formal arguments,
                    // each bound to the term of the argument given here.
                    const declaration = r.types.nominalDeclarationForPayload(nominal) orelse
                        invariant("a nominal with a backing has a declaration");
                    const formals = declaration.formalArgs(r.types);
                    if (formals.len != nominal.args.len) invariant("a nominal's arguments are its declaration's variables");
                    const backing_bindings = try gpa.alloc(TypeTerms.Binding, formals.len);
                    defer gpa.free(backing_bindings);
                    for (formals, nominal.args, backing_bindings) |formal, arg, *binding| {
                        const arg_term = try boundTerm(self.terms, gpa, r.types, arg, bindings);
                        try self.work.append(gpa, arg_term);
                        binding.* = .{ .variable = formal, .term = arg_term };
                    }
                    try self.work.append(gpa, try self.terms.intern(gpa, backing.?, backing_bindings));
                },
                .empty_record, .empty_tag_union, .pending, .err => {},
            }
        }
    }

    fn child(self: *ImplicitScan, id: CheckedTypeId, bindings: []const TypeTerms.Binding) Allocator.Error!void {
        try self.work.append(self.r.gpa, try boundTerm(self.terms, self.r.gpa, self.r.types, id, bindings));
    }

    /// Record an occurrence of each descriptor method of `nominal`, whose
    /// type is the term `owner`.
    fn nominalOccurrence(self: *ImplicitScan, s: *OccurrenceScan, expr: ExprId, nominal: checked.CheckedNominalType, owner: u32) Allocator.Error!void {
        const r = self.r;
        // A builtin's methods are Builtin's, which holds no Code site.
        if (nominal.builtin != null) return;
        const targets = try self.targetsOf(nominal);
        for (descriptor_methods, targets) |method, maybe_target| {
            const target = maybe_target orelse continue;
            const recorded_key: RecordedKey = .{ .template = if (s.template) |template| @backingInt(template) else Inventories.none, .method = method, .owner = owner };
            if ((try self.recorded.getOrPut(r.gpa, recorded_key)).found_existing) continue;
            try self.out.append(r.gpa, .{
                .method = method,
                .owner = owner,
                .expr = expr,
                .template = s.template,
                .template_vars = try self.termMentions(owner, s.template_vars),
                .local_vars = try self.termMentions(owner, &s.local_vars),
                .target = target,
            });
        }
    }

    /// Whether the term `term` mentions a variable of `vars`.
    fn termMentions(self: *ImplicitScan, term: u32, vars: *const Reifier.RowVars) Allocator.Error!bool {
        if (vars.count() == 0) return false;
        const bindings = self.terms.termBindings(term);
        if (bindings.len == 0) return self.r.mentionsAny(self.terms.terms.items[term].ty, vars);
        // A term with bindings is a backing, which reads only the
        // declaration's formal arguments.
        for (bindings) |binding| if (try self.termMentions(binding.term, vars)) return true;
        return false;
    }

    /// The template each descriptor method of `nominal` runs, read from the
    /// registry of the module that declares it, or null where it has none
    /// that can hold an inventory: a structural method, a method of a type
    /// a function body declares, or an intrinsic.
    fn targetsOf(self: *ImplicitScan, nominal: checked.CheckedNominalType) Allocator.Error![descriptor_methods.len]?ImplicitTarget {
        const r = self.r;
        const owner = r.foreignNominal(nominal);
        const memo = try self.nominals.getOrPut(r.gpa, .{ .module = owner.module.*, .decl = owner.source_decl });
        if (memo.found_existing) return memo.value_ptr.*;
        var targets: [descriptor_methods.len]?ImplicitTarget = @splat(null);
        if (try r.templateReader(.{ .bytes = nominal.owner_module.bytes })) |declaring| {
            for (descriptor_methods, &targets) |method, *slot| {
                const target = declaringMethod(declaring, owner, method) orelse continue;
                // A refused method is a rejected declaration for each call
                // the compiler makes (`refused_methods`).
                if (checked.registeredMethodKey(declaring.names, owner, method.text())) |key| {
                    const refused = if (declaring == r)
                        for (self.own_refused.items) |own| {
                            if (std.meta.eql(own.key, key)) break true;
                        } else false
                    else
                        (try declaring.codeInventories()).refusesMethod(key);
                    if (refused) continue;
                }
                slot.* = try implicitTargetOf(declaring, target);
            }
        }
        memo.value_ptr.* = targets;
        return targets;
    }
};

/// The target the registry of `declaring`, the module that declares a
/// nominal, records for one of its descriptor methods: inspection reads
/// only an eligible `to_inspect` (design.md "Inspect Overrides").
fn declaringMethod(declaring: *Reifier, owner: ForeignNominal, method: DescriptorMethod) ?static_dispatch.MethodTarget {
    const registry = declaring.sources.method_registry;
    return switch (method) {
        .to_inspect => checked.registeredInspectOverride(declaring.names, registry, owner),
        .is_eq, .to_hash => checked.registeredMethod(declaring.names, registry, owner, method.text()),
    };
}

/// The template a descriptor method target runs, or null for a target with
/// no body that can hold an inventory. `declaring` is the module whose
/// registry recorded the target.
fn implicitTargetOf(declaring: *Reifier, target: static_dispatch.MethodTarget) Allocator.Error!?ImplicitTarget {
    switch (target.kind) {
        .procedure => |procedure| {
            const reader = try declaring.templateReader(procedure.template.artifact) orelse return null;
            const template = reader.procedure_templates.templates.items[@backingInt(procedure.template.template)];
            const body = switch (template.body) {
                .checked_body => |root_expr| root_expr,
                .intrinsic_wrapper, .entry_wrapper, .unimplemented => return null,
            };
            return .{ .artifact = reader.artifact.bytes, .template = procedure.template.template, .body = body, .computed = false };
        },
        .callable_binding => |binding| {
            const reader = try declaring.templateReader(binding.module) orelse return null;
            const eval_template = reader.callable_eval_templates.templates[@backingInt(binding.template)];
            const wrapper = reader.entry_wrappers.lookupByRoot(eval_template.root) orelse
                invariant("a method bound to a computed callable has no entry wrapper");
            return .{ .artifact = reader.artifact.bytes, .template = wrapper.template.template, .body = eval_template.body, .computed = true };
        },
        // A method of a type a function body declares is a lambda of that
        // body, described with the body's own inventory.
        .local_proc, .structural => return null,
    }
}

/// Find this module's closing uses (D1), build each one's table, and refuse
/// the uses no table can serve: a use whose evidence selects a method the
/// description step refused (Q17), a use at the variables of a lambda a
/// block generalized (Q5), and a use whose table holds a refused
/// description. The uses are closed in node order.
fn closeWrittenUses(
    tables: *TableBuilder,
    scan: *const ModuleScan,
    roots: []const checked.CompileTimeRoot,
    closed: *std.ArrayList(ClosedEdge),
    refused: *std.ArrayList(RefusedUse),
) Allocator.Error!void {
    const reifier = tables.reifier;
    const gpa = tables.gpa;
    var ordered = std.ArrayList(Occurrence).empty;
    defer ordered.deinit(gpa);
    for (scan.occurrences.items) |occurrence| {
        if (occurrence.kind == .use) try ordered.append(gpa, occurrence);
    }
    std.mem.sort(Occurrence, ordered.items, {}, occurrenceLessThan);
    for (ordered.items) |occurrence| {
        const region = reifier.bodies.expr(occurrence.shown orelse occurrence.expr).source_region;
        if (try evidenceReachesRefused(reifier, occurrence.expr)) |method| {
            try refused.append(gpa, .{ .edge = occurrence.edge, .expr = occurrence.poison, .statement = occurrence.statement, .region = region, .rejection = .{
                .kind = method.kind,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = method.detail,
            } });
            continue;
        }
        // A use whose evidence selects a method with an inventory from a
        // type alone has no edge for its table. A use at its template's
        // variables is read the same way: the methods derived evidence
        // selects there are those of the dispatchers' owners, which the
        // template's types already name, and every closing use of the
        // template reaches them.
        if (!occurrence.local_vars and try tables.derivedEvidenceReachesInventory(occurrence.expr)) {
            try refused.append(gpa, .{ .edge = occurrence.edge, .expr = occurrence.poison, .statement = occurrence.statement, .region = region, .rejection = .{
                .kind = .instance_through_derived_evidence,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = "",
            } });
            continue;
        }
        const used = try reifier.usedTemplate(occurrence.expr) orelse continue;
        if ((try used.reader.codeInventories()).inventoryOf(used.template) == null) continue;
        if (occurrence.local_vars) {
            try refused.append(gpa, .{ .edge = occurrence.edge, .expr = occurrence.poison, .statement = occurrence.statement, .region = region, .rejection = .{
                .kind = .instance_in_local_generic,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = "",
            } });
            continue;
        }
        // A use at its own template's variables is a forward entry of that
        // template's inventory, which a closing use of the template reads.
        if (occurrence.template_vars) continue;
        try closeEdge(tables, roots, occurrence.edge, occurrence.expr, .{ .expr = occurrence.poison, .statement = occurrence.statement, .region = region }, closed, refused);
    }
}

/// Build the table of each closing edge of a use's evidence whose target
/// has an inventory (design.md "Code Instance Tables"), as for a written
/// use: an edge at the variables of a lambda a block generalized is refused
/// (Q5), and an edge at its template's own variables is a forward entry of
/// that template's inventory.
fn closeEvidenceEdges(
    tables: *TableBuilder,
    scan: *const ModuleScan,
    roots: []const checked.CompileTimeRoot,
    closed: *std.ArrayList(ClosedEdge),
    refused: *std.ArrayList(RefusedUse),
) Allocator.Error!void {
    const reifier = tables.reifier;
    for (scan.edges.items) |occurrence| {
        if (occurrence.template_vars and !occurrence.local_vars) continue;
        if (!try edgeHasInventory(reifier, null, occurrence.edge)) continue;
        const region = reifier.bodies.expr(occurrence.at).source_region;
        if (occurrence.local_vars) {
            try refused.append(tables.gpa, .{ .edge = occurrence.edge, .expr = occurrence.poison, .statement = occurrence.statement, .region = region, .rejection = .{
                .kind = .instance_in_local_generic,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = "",
            } });
            continue;
        }
        try closeEdge(tables, roots, occurrence.edge, occurrence.at, .{ .expr = occurrence.poison, .statement = occurrence.statement, .region = region }, closed, refused);
    }
}

/// Where the report of a refused closing edge stands and what a crash
/// replaces: the fields of `RefusedUse` besides the edge and the rejection.
const RefusalPlace = struct {
    expr: ExprId,
    statement: ?StatementId = null,
    region: base.Region,
};

/// Build the table of the closing edge `edge`, which stands at `at` in this
/// module, and record it, or its refusal when the table holds a refused
/// description. Every kind of closing edge is closed here. An edge two uses
/// share (a node that two method calls target, or that a call targets and
/// the evidence of another use reaches) is built at each use, which reports
/// its own refusal, and recorded once.
fn closeEdge(
    tables: *TableBuilder,
    roots: []const checked.CompileTimeRoot,
    edge: CodeEdge,
    at: ExprId,
    place: RefusalPlace,
    closed: *std.ArrayList(ClosedEdge),
    refused: *std.ArrayList(RefusedUse),
) Allocator.Error!void {
    const steps = [_]ChainStep{.{ .reader = tables.reifier, .edge = edge, .at = at }};
    const table = try tables.build(&steps);
    if (try tables.firstRejection(table)) |rejection| {
        try refused.append(tables.gpa, .{ .edge = edge, .expr = place.expr, .statement = place.statement, .region = place.region, .rejection = rejection });
        return;
    }
    const recorded = try tables.closed_edges.getOrPut(tables.gpa, CodeEdgeKey.of(edge));
    if (recorded.found_existing) {
        // An edge names one instance, and `build` shares the table of an
        // instance.
        std.debug.assert(recorded.value_ptr.* == table);
    } else {
        recorded.value_ptr.* = table;
        try closed.append(tables.gpa, .{ .edge = edge, .table = table });
        try tables.attachRoots(roots, edge, table);
    }
    if (base.dev_diagnostics.isSet(.reify_instances)) tables.printTable(place.region, table, 0);
}

/// Build the table of each platform requirement's closing use (design.md
/// "Code Instance Tables"), where the app binding's template has an
/// inventory. A requirement whose solution leaves a free variable with a
/// constraint is refused there: lowering seals the variable and ignores the
/// constraint.
fn closeRequirements(
    tables: *TableBuilder,
    roots: []const checked.CompileTimeRoot,
    closed: *std.ArrayList(ClosedEdge),
    refused: *std.ArrayList(RefusedUse),
) Allocator.Error!void {
    const reifier = tables.reifier;
    const gpa = tables.gpa;
    for (tables.requirements) |*requirement| {
        const region = reifier.bodies.expr(requirement.body).source_region;
        if (!try tables.requirementHasInventory(requirement, region)) continue;
        if (requirement.sealed == null) {
            try refused.append(gpa, .{ .edge = .{ .requirement = requirement.requires_idx }, .expr = requirement.body, .region = region, .rejection = .{
                .kind = .requirement_constrained_variable,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = "",
            } });
            continue;
        }
        try closeEdge(tables, roots, .{ .requirement = requirement.requires_idx }, requirement.body, .{ .expr = requirement.body, .region = region }, closed, refused);
    }
}

/// Build the table of each descriptor method at each type occurrence of a
/// closed type in this module's bodies (Q17, design.md "Code Instance
/// Tables"): the method's target at the owner type. An occurrence at the
/// variables of a lambda a block generalized is refused; an occurrence at
/// a template's own variables is an entry of its inventory.
fn closeImplicits(tables: *TableBuilder, scan: *const ModuleScan, refused: *std.ArrayList(RefusedImplicit)) Allocator.Error!void {
    const reifier = tables.reifier;
    const gpa = tables.gpa;
    const terms: TypeTerms = .{ .terms = scan.terms.terms.items, .bindings = scan.terms.bindings.items };
    // Each refused table is reported once, at its first occurrence.
    var reported: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer reported.deinit(gpa);
    for (scan.implicits.items) |occurrence| {
        if (occurrence.template_vars and !occurrence.local_vars) continue;
        if (!try implicitTargetHasInventory(reifier, null, occurrence.target)) continue;
        const region = reifier.bodies.expr(occurrence.expr).source_region;
        if (occurrence.local_vars) {
            try refused.append(gpa, .{ .region = region, .rejection = .{
                .kind = .instance_in_local_generic,
                .region = region,
                .module = reifier.rejectionModule(),
                .detail = "",
            } });
            continue;
        }
        const steps = [_]ChainStep{.{ .reader = reifier, .edge = .{ .use = occurrence.expr }, .at = occurrence.expr, .implicit = .{
            .method = occurrence.method,
            .terms = terms,
            .owner = occurrence.owner,
        } }};
        const table = try tables.build(&steps);
        if (try tables.firstRejection(table)) |rejection| {
            if (!(try reported.getOrPut(gpa, table)).found_existing) try refused.append(gpa, .{ .region = region, .rejection = rejection });
            continue;
        }
        if (base.dev_diagnostics.isSet(.reify_instances)) {
            std.debug.print("reify instances: {s} at {d}..{d}\n", .{ occurrence.method.text(), region.start.offset, region.end.offset });
            tables.printTable(region, table, 0);
        }
    }
}

/// A type occurrence of a descriptor method whose table is refused (Q17).
/// The description step reports it; the table's implicit instance records
/// the refusal for lowering.
pub const RefusedImplicit = struct {
    region: base.Region,
    rejection: Rejection,
};

/// The refusal of a method the description step refused (Q17) that the
/// evidence a use supplies selects at any depth, or null. Such a method is a
/// rejected declaration for each call (`refused_methods`): lowering reads it
/// as a checked error, so the use is refused with the method's rejection.
fn evidenceReachesRefused(reifier: *Reifier, use: ExprId) Allocator.Error!?Rejection {
    switch (reifier.bodies.expr(use).data) {
        .lookup_local, .lookup_external => {
            const entries = reifier.plans.siteEvidence(use) orelse return null;
            return evidenceEntriesReach(reifier, entries);
        },
        .numeral,
        .code_site,
        .str_segment,
        .str,
        .bytes_literal,
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
        => {
            const spec = (try reifier.dispatchOfUse(use)) orelse return null;
            const direct = switch (spec.resolution) {
                .direct_closed, .direct_parametric => |direct| direct,
                .direct_pending, .evidence_dependent, .structural, .checked_error, .@"unreachable" => return null,
            };
            const node = reifier.plans.evidenceNode(direct.evidence);
            return switch (node.nested) {
                .resolved => evidenceEntriesReach(reifier, reifier.plans.nestedEvidence(node)),
                .through_alias => aliasEvidenceReaches(reifier, node),
                .from_callable => null,
            };
        },
    }
}

/// `evidenceReachesRefused` for the evidence an edge through a method alias
/// supplies: what the edge answered for the alias's requirements, and what
/// each lookup of the alias chain records for the target's.
fn aliasEvidenceReaches(reifier: *Reifier, node: static_dispatch.EvidenceNode) Allocator.Error!?Rejection {
    if (try evidenceEntriesReach(reifier, reifier.plans.aliasScopeEvidence(node))) |found| return found;
    const alias = node.target.alias orelse invariant("an edge through a method alias names its alias");
    const alias_holder = try reifier.templateReader(alias.module) orelse return null;
    var hop = alias_holder.firstAliasHop(alias);
    while (true) {
        if (hop.reader.plans.siteEvidence(hop.lookup)) |entries| {
            if (try evidenceEntriesReach(hop.reader, entries)) |found| return found;
        }
        hop = try Reifier.nextAliasHop(hop) orelse return null;
    }
}

fn evidenceEntriesReach(reifier: *Reifier, entries: []const static_dispatch.CheckedEvidence) Allocator.Error!?Rejection {
    for (entries) |entry| {
        const node_id = switch (entry.resolution) {
            .direct => |node_id| node_id,
            .constraint, .structural, .from_callable, .from_scheme, .checked_error, .unreachable_value => continue,
        };
        const node = reifier.plans.evidenceNode(node_id);
        if (try refusedTargetOf(reifier, node)) |rejection| return rejection;
        switch (node.nested) {
            .resolved => if (try evidenceEntriesReach(reifier, reifier.plans.nestedEvidence(node))) |found| return found,
            .through_alias => if (try aliasEvidenceReaches(reifier, node)) |found| return found,
            .from_callable => {},
        }
    }
    return null;
}

/// The evidence nodes of the use `use` whose target derives its own
/// evidence from its callable (`from_callable`): in the evidence the use
/// supplies, at any depth, and the use's own dispatch target.
fn derivedNodesOfUse(reifier: *Reifier, use: ExprId, out: *std.ArrayList(static_dispatch.EvidenceNodeId)) Allocator.Error!void {
    if (reifier.plans.siteEvidence(use)) |entries| return derivedNodesOf(reifier, entries, out);
    const spec = (try reifier.dispatchOfUse(use)) orelse return;
    const direct = switch (spec.resolution) {
        .direct_closed, .direct_parametric => |direct| direct,
        .direct_pending, .evidence_dependent, .structural, .checked_error, .@"unreachable" => return,
    };
    try derivedNodesOfNode(reifier, direct.evidence, out);
}

fn derivedNodesOf(reifier: *Reifier, entries: []const static_dispatch.CheckedEvidence, out: *std.ArrayList(static_dispatch.EvidenceNodeId)) Allocator.Error!void {
    for (entries) |entry| switch (entry.resolution) {
        .direct => |node_id| try derivedNodesOfNode(reifier, node_id, out),
        .constraint, .structural, .from_callable, .from_scheme, .checked_error, .unreachable_value => {},
    };
}

fn derivedNodesOfNode(reifier: *Reifier, node_id: static_dispatch.EvidenceNodeId, out: *std.ArrayList(static_dispatch.EvidenceNodeId)) Allocator.Error!void {
    const node = reifier.plans.evidenceNode(node_id);
    switch (node.nested) {
        .resolved => try derivedNodesOf(reifier, reifier.plans.nestedEvidence(node), out),
        .through_alias => try derivedNodesOf(reifier, reifier.plans.aliasScopeEvidence(node), out),
        .from_callable => if (node.target.kind == .procedure) try out.append(reifier.gpa, node_id),
    }
}

/// The refusal of the target an evidence node names, where it is a method
/// of its dispatcher's nominal that the declaring module refused (Q17,
/// `CodeInventories.refused_methods`): the target its registry records for
/// the refused key.
fn refusedTargetOf(reifier: *Reifier, node: static_dispatch.EvidenceNode) Allocator.Error!?Rejection {
    const dispatcher = node.dispatcher_ty orelse return null;
    const settled = Reifier.settledType(reifier.resolvedType(dispatcher));
    const nominal = settled.reader.nominalOf(settled.id) orelse return null;
    if (nominal.builtin != null) return null;
    const declaring = try settled.reader.templateReader(.{ .bytes = nominal.owner_module.bytes }) orelse return null;
    const owner = settled.reader.foreignNominal(nominal);
    const owner_key: static_dispatch.MethodOwner = .{ .nominal = .{
        .module = declaring.names.lookupModuleIdentity(owner.module) orelse
            invariant("a nominal's declaring module does not name its own identity"),
        .source_decl = owner.source_decl,
    } };
    for ((try declaring.codeInventories()).refused_methods) |refused| {
        if (!std.meta.eql(refused.key.owner, owner_key)) continue;
        // The description step refuses only a method its registry binds.
        const target = switch (declaring.sources.method_registry.lookup(refused.key) orelse
            invariant("a refused method has no registry entry")) {
            .target => |target| target,
            .rejected => invariant("a refused method is a rejected registry entry"),
        };
        if (std.meta.eql(target.kind, node.target.kind) and std.meta.eql(target.alias, node.target.alias)) return refused.rejection;
    }
    return null;
}

/// The generalized local function scope an edge of a requirement chain
/// enters: a use of the local function, or its construction.
fn localScopeOfEdge(reader: *Reifier, expr: ExprId) ?*const checked.DispatchRefScope {
    const templates = reader.procedure_templates;
    if (reader.value_refs.lookupIdByExpr(expr)) |id| switch (reader.value_refs.records[@backingInt(id)].ref) {
        .local_proc => |local| if (local.dispatch_scope) |scope| return &templates.dispatch_scopes[@backingInt(scope)],
        .local_param, .local_value, .local_mutable_version, .pattern_binder, .selected_hoisted_const, .top_level_const, .imported_const, .top_level_proc, .imported_proc, .hosted_proc, .platform_required_declaration, .platform_required_const, .platform_required_proc, .platform_required_checked_error, .promoted_top_level_proc => {},
    };
    for (templates.dispatch_scopes) |*scope| {
        if (scope.checked_expr == expr) return scope;
    }
    return null;
}

/// One edge on the way from a closing edge to a table's template: the
/// reader of the module that holds the edge, the edge, and the expression
/// it stands at, where a report about it points.
const ChainStep = struct {
    reader: *Reifier,
    /// A use, an edge of a use's evidence, whose `at` is then that use, or
    /// a platform requirement of the first step's module, whose `at` is then
    /// its binding's definition.
    edge: CodeEdge,
    at: ExprId,
    /// For a type occurrence of a descriptor method (Q17), the method and
    /// the owner type; `at` is then the expression whose type holds it, and
    /// `edge` is its use.
    implicit: ?ImplicitStep = null,
};

/// A type occurrence of a descriptor method as a step of a chain (Q17): the
/// method, and the owner type, a term of `terms` in the store of the
/// step's reader.
const ImplicitStep = struct {
    method: DescriptorMethod,
    terms: TypeTerms,
    owner: u32,
};

/// The instance a chain of uses reaches: the template, read by its module's
/// reader, the frame that holds what the chain fixed its variables to, the
/// instance's key, and the evidence the last use supplied.
const Established = struct {
    reader: *Reifier,
    template: canonical.CheckedProcedureTemplateId,
    frame: Reifier.FrameId,
    key: [32]u8,
    evidence: Reifier.SuppliedEvidence,
    /// For a chain that ends at a type occurrence (Q17), the owner type.
    owner: ?Reifier.FramedType = null,
};

/// What a reader held before a chain set its instance, restored when the
/// walk ends.
const SavedStates = struct {
    gpa: Allocator,
    saved: std.ArrayList(Saved) = .empty,

    const Saved = struct {
        reader: *Reifier,
        frame: Reifier.FrameId,
        evidence: Reifier.SuppliedEvidence,
        instance_key: [32]u8,
    };

    fn set(self: *SavedStates, reader: *Reifier, frame: Reifier.FrameId, evidence: Reifier.SuppliedEvidence, key: [32]u8) Allocator.Error!void {
        try self.saved.append(self.gpa, .{ .reader = reader, .frame = reader.frame, .evidence = reader.evidence, .instance_key = reader.instance_key });
        reader.frame = frame;
        reader.evidence = evidence;
        reader.instance_key = key;
    }

    fn restore(self: *SavedStates) void {
        while (self.saved.pop()) |saved| {
            saved.reader.frame = saved.frame;
            saved.reader.evidence = saved.evidence;
            saved.reader.instance_key = saved.instance_key;
        }
        self.saved.deinit(self.gpa);
    }
};

/// The tables a module's closing uses build (D1). A table is keyed by its
/// template and the key of its instance, so two uses at one type share one,
/// and a recursive use at the template's own types names the table being
/// built: the tables are a graph.
const TableBuilder = struct {
    gpa: Allocator,
    walk: *Walk,
    /// The reader of the module whose closing uses are built.
    reifier: *Reifier,
    /// The platform requirements of `reifier`'s module, which a
    /// `requirement` edge names by requires index.
    requirements: []const RequirementUse = &.{},
    tables: std.ArrayList(InstanceTables.Span) = .empty,
    /// The template each of `tables` serves.
    templates: std.ArrayList(InstanceTables.TableTemplate) = .empty,
    entries: std.ArrayList(InstanceTables.TableEntry) = .empty,
    reads: std.ArrayList(checked.CheckedCodeRead) = .empty,
    /// The refusal of each table, or null.
    rejections: std.ArrayList(?Rejection) = .empty,
    memo: std.AutoHashMapUnmanaged(MemoKey, u32) = .empty,
    /// The closing edges recorded with a table (`closeEdge`), and the table.
    closed_edges: std.AutoHashMapUnmanaged(CodeEdgeKey, u32) = .empty,
    /// Each table's span of `bound_entries`, parallel to `tables`.
    table_bounds: std.ArrayList(InstanceTables.Span) = .empty,
    bound_entries: std.ArrayList(InstanceTables.BoundEntry) = .empty,
    /// The reader of each table's template's module, parallel to `tables`;
    /// null for a refused table.
    readers: std.ArrayList(?*Reifier) = .empty,
    root_bounds: std.ArrayList(InstanceTables.RootBound) = .empty,
    slots: std.ArrayList(checked.CheckedCodeSlot) = .empty,
    slot_steps: std.ArrayList(checked.CheckedCodeSlotStep) = .empty,
    slot_shapes: std.ArrayList(u32) = .empty,
    first_slots: std.ArrayList(u32) = .empty,
    implicit_instances: std.ArrayList(InstanceTables.ImplicitInstance) = .empty,
    owner_terms: std.ArrayList(InstanceTables.OwnerTerm) = .empty,
    owner_bindings: std.ArrayList(InstanceTables.OwnerBinding) = .empty,
    owner_members: std.ArrayList(InstanceTables.OwnerMember) = .empty,
    owner_member_terms: std.ArrayList(u32) = .empty,
    owner_modules: std.ArrayList(checked.CheckedModuleArtifactKey) = .empty,
    /// The tables `implicit_instances` holds, by method.
    implicit_seen: std.AutoHashMapUnmanaged(struct { method: DescriptorMethod, table: u32 }, void) = .empty,

    const MemoKey = struct {
        module: [32]u8,
        template: u32,
        key: [32]u8,
    };

    /// `ROC_REIFY_INSTANCES`: a closing use at `region` and its table, one
    /// line per entry, a nested table indented under its forward entry.
    /// A table the tables above already print, as a recursive table is, or
    /// a table 64 levels down is printed by its number only.
    fn printTable(self: *const TableBuilder, region: base.Region, table: u32, depth: usize) void {
        var above: [64]u32 = undefined;
        self.printTableIn(region, table, depth, &above);
    }

    fn tableIsAbove(above: []const u32, table: u32) bool {
        for (above) |ancestor| {
            if (ancestor == table) return true;
        }
        return false;
    }

    fn printTableIn(self: *const TableBuilder, region: base.Region, table: u32, depth: usize, above: *[64]u32) void {
        if (depth == 0) std.debug.print("reify instances: use at {d}..{d}, table {d}\n", .{ region.start.offset, region.end.offset, table });
        above[depth] = table;
        const span = self.tables.items[table];
        for (self.entries.items[span.start..][0..span.len], 0..) |entry, index| {
            for (0..depth + 1) |_| std.debug.print("  ", .{});
            switch (entry.kind) {
                .node => std.debug.print("{d}: node {d}\n", .{ index, entry.value }),
                .table => {
                    if (tableIsAbove(above[0 .. depth + 1], entry.value)) {
                        std.debug.print("{d}: table {d} (above)\n", .{ index, entry.value });
                        continue;
                    }
                    if (depth + 1 == above.len) {
                        std.debug.print("{d}: table {d} (too deep to print)\n", .{ index, entry.value });
                        continue;
                    }
                    std.debug.print("{d}: table {d}\n", .{ index, entry.value });
                    self.printTableIn(region, entry.value, depth + 1, above);
                },
            }
        }
        const bounds = self.table_bounds.items[table];
        for (self.bound_entries.items[bounds.start..][0..bounds.len]) |bound| {
            for (0..depth + 1) |_| std.debug.print("  ", .{});
            std.debug.print("bound call {d}: {d} slots, first slots", .{ bound.call, bound.slots.len });
            for (self.first_slots.items[bound.first_slots.start..][0..bound.first_slots.len]) |first| std.debug.print(" {d}", .{first});
            std.debug.print("\n", .{});
        }
    }

    fn deinit(self: *TableBuilder) void {
        self.tables.deinit(self.gpa);
        self.templates.deinit(self.gpa);
        self.entries.deinit(self.gpa);
        self.reads.deinit(self.gpa);
        self.rejections.deinit(self.gpa);
        self.memo.deinit(self.gpa);
        self.closed_edges.deinit(self.gpa);
        self.table_bounds.deinit(self.gpa);
        self.bound_entries.deinit(self.gpa);
        self.readers.deinit(self.gpa);
        self.root_bounds.deinit(self.gpa);
        self.slots.deinit(self.gpa);
        self.slot_steps.deinit(self.gpa);
        self.slot_shapes.deinit(self.gpa);
        self.first_slots.deinit(self.gpa);
        self.implicit_instances.deinit(self.gpa);
        self.owner_terms.deinit(self.gpa);
        self.owner_bindings.deinit(self.gpa);
        self.owner_members.deinit(self.gpa);
        self.owner_member_terms.deinit(self.gpa);
        self.owner_modules.deinit(self.gpa);
        self.implicit_seen.deinit(self.gpa);
    }

    /// Record that `table` is `method`'s table at the owner type `owner`
    /// (an `owner_terms` index), once per table (Q17).
    fn recordImplicit(self: *TableBuilder, method: DescriptorMethod, owner: u32, table: u32) Allocator.Error!void {
        if ((try self.implicit_seen.getOrPut(self.gpa, .{ .method = method, .table = table })).found_existing) return;
        try self.implicit_instances.append(self.gpa, .{ .method = method, .owner = owner, .table = table });
    }

    /// The owner term of `framed`: its type in its store, with the term of
    /// what its frame fixes each variable it mentions to (Q17).
    ///
    /// A frame binds a row variable to the whole row a use matched
    /// (`Reifier.matchRecord`), but the variable stands for the rest of that
    /// row only. So a variable that ends a row whose nearer links name labels
    /// is bound to a row term of exactly the rest: the members of the bound
    /// row that no nearer link names. Lowering substitutes a binding as is.
    fn ownerTerm(self: *TableBuilder, framed: Reifier.FramedType) Allocator.Error!u32 {
        const reader = framed.reader;
        var vars: Reifier.RowVars = .empty;
        defer vars.deinit(self.gpa);
        try reader.collectVars(framed.id, &vars);
        var bound = std.ArrayList(InstanceTables.OwnerBinding).empty;
        defer bound.deinit(self.gpa);
        var field_labels = std.ArrayList(canonical.RecordFieldLabelId).empty;
        defer field_labels.deinit(self.gpa);
        var tag_labels = std.ArrayList(canonical.TagLabelId).empty;
        defer tag_labels.deinit(self.gpa);
        var keys = vars.keyIterator();
        while (keys.next()) |variable| {
            const fixed = reader.fixedTypeIn(framed.frame, variable.*) orelse continue;
            field_labels.clearRetainingCapacity();
            tag_labels.clearRetainingCapacity();
            try reader.nearerRowLabels(framed.id, variable.*, &field_labels, &tag_labels);
            const term = if (field_labels.items.len != 0)
                try self.ownerRecordRest(reader, field_labels.items, fixed)
            else if (tag_labels.items.len != 0)
                try self.ownerTagRest(reader, tag_labels.items, fixed)
            else
                try self.ownerTerm(fixed);
            try bound.append(self.gpa, .{ .variable = variable.*, .term = term });
        }
        std.mem.sort(InstanceTables.OwnerBinding, bound.items, {}, struct {
            fn lessThan(_: void, a: InstanceTables.OwnerBinding, b: InstanceTables.OwnerBinding) bool {
                return @backingInt(a.variable) < @backingInt(b.variable);
            }
        }.lessThan);
        const module = try self.ownerModule(reader);
        const start: u32 = @intCast(self.owner_bindings.items.len);
        try self.owner_bindings.appendSlice(self.gpa, bound.items);
        try self.owner_terms.append(self.gpa, .{ .module = module, .ty = framed.id, .bindings = .{ .start = start, .len = @intCast(bound.items.len) } });
        return @intCast(self.owner_terms.items.len - 1);
    }

    /// The `owner_modules` index of `reader`'s module.
    fn ownerModule(self: *TableBuilder, reader: *Reifier) Allocator.Error!u32 {
        for (self.owner_modules.items, 0..) |key, at| {
            if (std.meta.eql(key.bytes, reader.artifact.bytes)) return @intCast(at);
        }
        try self.owner_modules.append(self.gpa, reader.artifact);
        return @intCast(self.owner_modules.items.len - 1);
    }

    /// The row term of the fields of the record `fixed` that none of
    /// `labels` (labels of `labels_reader`'s store) names (Q17).
    ///
    /// A row that a generic caller wrote ends at its own row variable, which
    /// the caller's frame binds to the whole row its use matched in turn. So
    /// the rest goes on through each such binding, and each step leaves out
    /// the fields that the row of the step before names.
    fn ownerRecordRest(
        self: *TableBuilder,
        labels_reader: *Reifier,
        labels: []const canonical.RecordFieldLabelId,
        fixed: Reifier.FramedType,
    ) Allocator.Error!u32 {
        var members = std.ArrayList(InstanceTables.OwnerMember).empty;
        defer members.deinit(self.gpa);
        var terms = std.ArrayList(u32).empty;
        defer terms.deinit(self.gpa);
        var named_by = labels_reader;
        var named = std.ArrayList(canonical.RecordFieldLabelId).empty;
        defer named.deinit(self.gpa);
        try named.appendSlice(self.gpa, labels);
        var fields = std.ArrayList(checked.CheckedRecordField).empty;
        defer fields.deinit(self.gpa);
        var current = fixed;
        while (true) {
            const reader = current.reader;
            const record = switch (reader.types.payload(current.id)) {
                .record => |record| record,
                .field_kind, .alias, .function, .nominal, .tuple, .tag_union, .empty_record, .empty_tag_union, .flex, .rigid, .pending, .err => invariant("a frame binds a row variable that ends a record row to no record"),
            };
            fields.clearRetainingCapacity();
            try reader.recordFields(&fields, record.fields, record.ext);
            const module = try self.ownerModule(reader);
            for (fields.items) |field| {
                const is_named = for (named.items) |label| {
                    if (named_by.sameFieldLabel(label, reader, field.name)) break true;
                } else false;
                if (is_named) continue;
                const term = try self.ownerTerm(reader.resolvedTypeIn(current.frame, field.ty));
                try members.append(self.gpa, .{ .module = module, .label = @backingInt(field.name), .kind = field.kind, .terms = .{ .start = @intCast(terms.items.len), .len = 1 } });
                try terms.append(self.gpa, term);
            }
            const tail = reader.recordRowTail(record.ext) orelse {
                // An owner term is built for a closed occurrence, so a row
                // that ends at no variable is closed.
                std.debug.assert(reader.rowEndIsEmpty(record.ext));
                break;
            };
            current = reader.fixedTypeIn(current.frame, tail) orelse invariant("an owner term's row ends at a variable no frame fixes");
            named_by = reader;
            named.clearRetainingCapacity();
            for (fields.items) |field| try named.append(self.gpa, field.name);
        }
        return try self.appendRowTerm(fixed.reader, .record_rest, fixed.id, members.items, terms.items);
    }

    /// The row term of the tags of the tag union `fixed` that none of
    /// `labels` (labels of `labels_reader`'s store) names (Q17), through
    /// each binding of a row variable it ends at, as `ownerRecordRest`.
    fn ownerTagRest(
        self: *TableBuilder,
        labels_reader: *Reifier,
        labels: []const canonical.TagLabelId,
        fixed: Reifier.FramedType,
    ) Allocator.Error!u32 {
        var members = std.ArrayList(InstanceTables.OwnerMember).empty;
        defer members.deinit(self.gpa);
        var terms = std.ArrayList(u32).empty;
        defer terms.deinit(self.gpa);
        var named_by = labels_reader;
        var named = std.ArrayList(canonical.TagLabelId).empty;
        defer named.deinit(self.gpa);
        try named.appendSlice(self.gpa, labels);
        var tags = std.ArrayList(checked.CheckedTag).empty;
        defer tags.deinit(self.gpa);
        var current = fixed;
        while (true) {
            const reader = current.reader;
            const union_ty = switch (reader.types.payload(current.id)) {
                .tag_union => |union_ty| union_ty,
                .field_kind, .alias, .function, .nominal, .tuple, .record, .empty_record, .empty_tag_union, .flex, .rigid, .pending, .err => invariant("a frame binds a row variable that ends a tag row to no tag union"),
            };
            tags.clearRetainingCapacity();
            try reader.unionTags(&tags, union_ty.tags, union_ty.ext);
            const module = try self.ownerModule(reader);
            for (tags.items) |tag| {
                const is_named = for (named.items) |label| {
                    if (named_by.sameTagLabel(label, reader, tag.name)) break true;
                } else false;
                if (is_named) continue;
                const start: u32 = @intCast(terms.items.len);
                for (tag.args) |arg| try terms.append(self.gpa, try self.ownerTerm(reader.resolvedTypeIn(current.frame, arg)));
                try members.append(self.gpa, .{ .module = module, .label = @backingInt(tag.name), .terms = .{ .start = start, .len = @intCast(tag.args.len) } });
            }
            const tail = reader.tagRowTail(union_ty.ext) orelse {
                // An owner term is built for a closed occurrence, so a row
                // that ends at no variable is closed.
                std.debug.assert(reader.rowEndIsEmpty(union_ty.ext));
                break;
            };
            current = reader.fixedTypeIn(current.frame, tail) orelse invariant("an owner term's row ends at a variable no frame fixes");
            named_by = reader;
            named.clearRetainingCapacity();
            for (tags.items) |tag| try named.append(self.gpa, tag.name);
        }
        return try self.appendRowTerm(fixed.reader, .tag_rest, fixed.id, members.items, terms.items);
    }

    /// Append a row term of `reader`'s module: `members`, whose term spans
    /// index `terms`.
    fn appendRowTerm(
        self: *TableBuilder,
        reader: *Reifier,
        kind: InstanceTables.OwnerTermKind,
        ty: CheckedTypeId,
        members: []const InstanceTables.OwnerMember,
        terms: []const u32,
    ) Allocator.Error!u32 {
        const module = try self.ownerModule(reader);
        const terms_start: u32 = @intCast(self.owner_member_terms.items.len);
        try self.owner_member_terms.appendSlice(self.gpa, terms);
        const members_start: u32 = @intCast(self.owner_members.items.len);
        for (members) |member| {
            var moved = member;
            moved.terms.start += terms_start;
            try self.owner_members.append(self.gpa, moved);
        }
        try self.owner_terms.append(self.gpa, .{
            .module = module,
            .kind = kind,
            .ty = ty,
            .bindings = .{},
            .members = .{ .start = members_start, .len = @intCast(members.len) },
        });
        return @intCast(self.owner_terms.items.len - 1);
    }

    /// Append `sources` to the slot pools, in slot order, and return their
    /// span of `slots`.
    fn appendSlots(self: *TableBuilder, sources: []const SlotSource) Allocator.Error!InstanceTables.Span {
        const start: u32 = @intCast(self.slots.items.len);
        for (sources) |slot| {
            const steps_start: u32 = @intCast(self.slot_steps.items.len);
            for (slot.steps) |step| try self.slot_steps.append(self.gpa, slotStepRecord(step));
            const shape_start: u32 = @intCast(self.slot_shapes.items.len);
            try self.slot_shapes.appendSlice(self.gpa, slot.shape);
            try self.slots.append(self.gpa, .{
                .source = slot.source,
                .steps_start = steps_start,
                .steps_len = @intCast(slot.steps.len),
                .shape_start = shape_start,
                .shape_len = @intCast(slot.shape.len),
                .encoder = if (slot.encoder) |encoder| .some(encoder) else .none,
            });
        }
        return .{ .start = start, .len = @intCast(sources.len) };
    }

    /// The platform requirement a `requirement` edge names.
    fn requirementAt(self: *const TableBuilder, requires_idx: u32) *const RequirementUse {
        for (self.requirements) |*candidate| {
            if (candidate.requires_idx == requires_idx) return candidate;
        }
        invariant("a requirement edge names no platform requirement of its module");
    }

    /// Fix the instance `chain` reaches in a walk begun by the caller.
    fn establish(self: *TableBuilder, chain: []const ChainStep, saved: *SavedStates) Reifier.Error!Established {
        var frame: Reifier.FrameId = Reifier.empty_frame;
        var key: [32]u8 = @splat(0);
        var evidence: Reifier.SuppliedEvidence = .{};
        var reader: *Reifier = undefined;
        var body: ExprId = undefined;
        var owner: ?Reifier.FramedType = null;
        for (chain, 0..) |step, index| {
            if (index != 0) try saved.set(step.reader, frame, evidence, key);
            self.walk.body = step.reader;
            const region = step.reader.bodies.expr(step.at).source_region;
            if (step.implicit) |implicit| {
                // The holder's frame fixes the owner type's variables.
                const owner_ty = try step.reader.termType(implicit.terms, implicit.owner, frame);
                const instance = try Reifier.implicitInstance(owner_ty, implicit.method, region);
                frame = instance.frame;
                key = instance.key;
                evidence = .{};
                reader = instance.reader;
                body = instance.body;
                owner = owner_ty;
                continue;
            }
            owner = null;
            var target = switch (step.edge) {
                .use => |use| (try step.reader.useTarget(use, region)) orelse
                    invariant("a use an inventory or a closing use names reaches no template"),
                .requirement => |requires_idx| try step.reader.requirementTarget(self.requirementAt(requires_idx), region),
                .node, .derivation_call => try self.evidenceEdgeTarget(step, saved, region),
                .literal => invariant("a chain step is a use, a platform requirement or an evidence edge"),
            };
            defer step.reader.releaseBound(target.bound);
            defer if (target.instantiation) |*fixed| fixed.substitution.deinit(self.gpa);
            frame = try target.reader.instanceFrame(target.instantiation, target.signature, target.key.body, target.key.curried);
            key = if (target.instantiation) |fixed| fixed.key else @splat(0);
            evidence = target.evidence;
            reader = target.reader;
            body = target.key.body;
        }
        return .{
            .reader = reader,
            .template = templateOfBody(reader, body) orelse invariant("a template with an inventory has a checked body"),
            .frame = frame,
            .key = key,
            .evidence = evidence,
            .owner = owner,
        };
    }

    /// The target an edge of a use's evidence selects, as the walk reads the
    /// node of a dispatch (`Reifier.dispatchTarget`). A contract call's node
    /// is over the variables its contract renamed, so the walk first binds
    /// each one to the type of the relation it renamed.
    fn evidenceEdgeTarget(self: *TableBuilder, step: ChainStep, saved: *SavedStates, region: base.Region) Reifier.Error!Reifier.CalleeTarget {
        const reader = step.reader;
        const node_id = switch (step.edge) {
            .node => |id| id,
            .derivation_call => |call| blk: {
                const contract = reader.plans.generated_codec_derivations[@backingInt(call.derivation)];
                var bound = try reader.walk.frameSubstitution(reader.frame).clone(self.gpa);
                defer bound.deinit(self.gpa);
                for (contract.renamedVarsSlice(reader.plans)) |pair| try bound.put(self.gpa, pair.copy, reader.resolvedType(pair.original));
                try saved.set(reader, try reader.walk.pushFrame(bound), reader.evidence, reader.instance_key);
                break :blk call.node;
            },
            .use, .requirement, .literal => unreachable, // the caller passes an evidence edge
        };
        const node = reader.plans.evidenceNode(node_id);
        const edge: Reifier.DispatchEdge = .{ .reader = reader, .node = node, .scope = reader.evidence };
        return switch (try reader.methodTargetCallee(reader, node.target, .{ .edge = edge }, region, .instance_table)) {
            .definition => |target| target,
            .provided, .foreign, .none => invariant("an evidence edge an inventory or a closing edge names reaches no template"),
        };
    }

    /// The table of the instance `chain` reaches, built or shared. A refusal
    /// is recorded on the table rather than returned, because a table a
    /// recursive use shares is still being built when the use names it.
    fn build(self: *TableBuilder, chain: []const ChainStep) Allocator.Error!u32 {
        self.walk.beginSite(.graph, false, self.reifier);
        try self.walk.startSite();
        var saved = SavedStates{ .gpa = self.gpa };
        const reached = self.establish(chain, &saved);
        saved.restore();
        const est = reached catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.Rejected => return self.refusedTable(self.walk.rejection.?),
            error.Diverged => invariant("a divergence escaped before any row was built"),
        };
        const memo_key = MemoKey{ .module = est.reader.artifact.bytes, .template = @backingInt(est.template), .key = est.key };
        const implicit_method: ?DescriptorMethod = if (chain[chain.len - 1].implicit) |implicit| implicit.method else null;
        // The owner type is read in the frames the chain pushed, which the
        // next walk drops.
        const implicit_owner: ?u32 = if (est.owner) |owner| try self.ownerTerm(owner) else null;
        if (self.memo.get(memo_key)) |existing| {
            if (implicit_method) |method| try self.recordImplicit(method, implicit_owner.?, existing);
            return existing;
        }
        const index: u32 = @intCast(self.tables.items.len);
        try self.tables.append(self.gpa, .{});
        try self.templates.append(self.gpa, .{ .module = est.reader.artifact, .template = @backingInt(est.template) });
        try self.readers.append(self.gpa, est.reader);
        try self.rejections.append(self.gpa, null);
        try self.table_bounds.append(self.gpa, .{});
        try self.memo.put(self.gpa, memo_key, index);
        if (implicit_method) |method| try self.recordImplicit(method, implicit_owner.?, index);

        const holder = est.reader;
        const inventories = try holder.codeInventories();
        const inventory = inventories.inventoryOf(est.template) orelse
            invariant("a closing use or a forward entry names a template with no inventory");
        var entries = std.ArrayList(InstanceTables.TableEntry).empty;
        defer entries.deinit(self.gpa);
        for (inventories.inventoryEntries(inventory)) |entry| switch (entry.kind) {
            .site => {
                const recipe = inventories.recipes[entry.recipe];
                // A site of a bound call is described below, with the
                // call's other sites, in site order.
                if (recipe.bound != Inventories.none) {
                    try entries.append(self.gpa, .{ .kind = .node, .value = 0, .reads = .{} });
                    continue;
                }
                const outcome = try self.describe(chain, holder, entry.node, recipe, null);
                const reads = try self.walk.takeReads();
                defer self.gpa.free(reads);
                switch (outcome) {
                    .reified => |node| {
                        const reads_start: u32 = @intCast(self.reads.items.len);
                        try self.reads.appendSlice(self.gpa, reads);
                        try entries.append(self.gpa, .{
                            .kind = .node,
                            .value = @backingInt(node),
                            .reads = .{ .start = reads_start, .len = @intCast(reads.len) },
                        });
                    },
                    .rejected => |rejection| {
                        self.rejections.items[index] = rejection;
                        break;
                    },
                }
            },
            .forward, .implicit => {
                const nested = try self.gpa.alloc(ChainStep, chain.len + 1);
                defer self.gpa.free(nested);
                @memcpy(nested[0..chain.len], chain);
                nested[chain.len] = .{
                    .reader = holder,
                    .edge = switch (entry.kind) {
                        .forward => inventories.forward_edges[entry.recipe],
                        .implicit => .{ .use = entry.node },
                        .site => unreachable, // the arm above takes a site
                    },
                    .at = entry.node,
                    .implicit = switch (entry.kind) {
                        .forward => null,
                        // The descriptor method's table at the owner type this
                        // instance fixes (Q17).
                        .implicit => .{
                            .method = inventories.implicits[entry.recipe].method,
                            .terms = inventories.terms,
                            .owner = inventories.implicits[entry.recipe].owner,
                        },
                        .site => unreachable, // the arm above takes a site
                    },
                };
                const child = try self.build(nested);
                try entries.append(self.gpa, .{ .kind = .table, .value = child, .reads = .{} });
            },
        };
        if (self.rejections.items[index] != null) {
            // A refused table serves no use, so, as `refusedTable`, it
            // records no template and no entry.
            self.templates.items[index] = .{ .module = .{}, .template = InstanceTables.none };
            self.readers.items[index] = null;
            return index;
        }
        try self.bindInstance(chain, holder, est.template, index, entries.items);
        const start: u32 = @intCast(self.entries.items.len);
        try self.entries.appendSlice(self.gpa, entries.items);
        self.tables.items[index] = .{ .start = start, .len = @intCast(entries.items.len) };
        return index;
    }

    fn refusedTable(self: *TableBuilder, rejection: Rejection) Allocator.Error!u32 {
        const index: u32 = @intCast(self.tables.items.len);
        try self.tables.append(self.gpa, .{});
        try self.table_bounds.append(self.gpa, .{});
        try self.templates.append(self.gpa, .{ .module = .{}, .template = InstanceTables.none });
        try self.readers.append(self.gpa, null);
        try self.rejections.append(self.gpa, rejection);
        return index;
    }

    /// Whether the template a platform requirement's app binding reaches has
    /// an inventory, so its closing use needs a table.
    fn requirementHasInventory(self: *TableBuilder, requirement: *const RequirementUse, region: base.Region) Allocator.Error!bool {
        if (try self.computedRequirementInventory(requirement)) |has_inventory| return has_inventory;
        self.walk.beginSite(.graph, false, self.reifier);
        try self.walk.startSite();
        const reached = self.reifier.reachedProcedure(.{ .top_level = requirement.binding }, requirement.binder, region) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            // A binding the walk cannot follow has no inventory to read.
            error.Rejected, error.Diverged => return false,
        };
        return (try reached.reader.codeInventories()).inventoryOf(reached.template.template_id) != null;
    }

    /// Whether the evidence of the closing use `use` holds a node whose
    /// target derives its own evidence from its callable (`from_callable`),
    /// and a method that evidence selects from a type, at any depth, holds an
    /// inventory (design.md "Code Instance Tables"). No checked node names
    /// such a method, so no edge keys its table; both lowerings select it
    /// from the method registry of the dispatcher's owner, as this reads it.
    fn derivedEvidenceReachesInventory(self: *TableBuilder, use: ExprId) Allocator.Error!bool {
        const reifier = self.reifier;
        var derived = std.ArrayList(static_dispatch.EvidenceNodeId).empty;
        defer derived.deinit(self.gpa);
        try derivedNodesOfUse(reifier, use, &derived);
        if (derived.items.len == 0) return false;
        self.walk.beginSite(.graph, false, reifier);
        try self.walk.startSite();
        var visited: std.AutoHashMapUnmanaged(DerivedKey, void) = .empty;
        defer visited.deinit(self.gpa);
        for (derived.items) |node_id| {
            const node = reifier.plans.evidenceNode(node_id);
            const procedure = switch (node.target.kind) {
                .procedure => |procedure| procedure,
                .callable_binding, .local_proc, .structural => invariant("a derived evidence node of a use names a procedure"),
            };
            // The node relates its target to the callable it records, which
            // fixes the target's variables as the lowerings fix them.
            const callable = switch (node.instantiation) {
                .callable, .alias, .derived_from_callable => |callable| reifier.resolvedType(callable),
                .monomorphic => null,
            };
            if (try self.derivedReaches(reifier, procedure.template, if (callable) |ty| .{ .callable = ty } else .none, &visited)) return true;
        }
        return false;
    }

    /// One instance a derived evidence walk has read.
    const DerivedKey = struct { artifact: [32]u8, template: u32, instantiation: [32]u8 };

    /// What fixes the variables of a template a derived evidence walk reads.
    const DerivedFix = union(enum) {
        /// The function type the edge related the template to.
        callable: Reifier.FramedType,
        /// The receiver whose owner selected the method, which fills the
        /// template's first parameter.
        receiver: Reifier.FramedType,
        /// The template has one type.
        none,
    };

    /// Whether the template `ref` names, at the instance `fix` gives, selects
    /// from a type a method that holds an inventory, at any depth. The
    /// template itself is counted only where a type selected it
    /// (`fix == .receiver`): a node names a template it relates to a
    /// callable, so an edge keys its table. A requirement whose dispatcher
    /// another requirement's result fixes is read after that requirement
    /// (`relateDerivedEvidence`).
    fn derivedReaches(
        self: *TableBuilder,
        owner: *Reifier,
        ref: canonical.ProcedureTemplateRef,
        fix: DerivedFix,
        visited: *std.AutoHashMapUnmanaged(DerivedKey, void),
    ) Allocator.Error!bool {
        const reader = try owner.templateReader(ref.artifact) orelse return false;
        if (fix == .receiver and (try reader.codeInventories()).inventoryOf(ref.template) != null) return true;
        const template = reader.procedure_templates.templates.items[@backingInt(ref.template)];
        const scheme_vars = reader.schemeVars(template);
        var substitution: Reifier.Substitution = .empty;
        defer substitution.deinit(self.gpa);
        switch (fix) {
            .callable => |callable| try reader.matchType(&substitution, scheme_vars, template.checked_fn_root, callable),
            .receiver => |receiver| {
                const function = reader.functionOf(template.checked_fn_root) orelse return false;
                if (function.args.len == 0) return false;
                try reader.matchType(&substitution, scheme_vars, function.args[0], receiver);
            },
            .none => {},
        }
        // A dispatcher that another requirement's result fixes (the
        // receiver of `x.pred().is_odd()`) is fixed as the lowerings fix it.
        var deriving: std.ArrayList(Reifier.DerivingKey) = .empty;
        defer deriving.deinit(self.gpa);
        try reader.relateDerivedEvidence(template, &substitution, &deriving);
        const key = try Reifier.instantiationKey(substitution, scheme_vars);
        if ((try visited.getOrPut(self.gpa, .{ .artifact = ref.artifact.bytes, .template = @backingInt(ref.template), .instantiation = key })).found_existing) return false;
        const frame = try self.walk.pushFrame(substitution);
        for (reader.procedure_templates.evidenceParams(&template)) |param| {
            // The dispatcher's owner selects the method, as both lowerings
            // select it for an edge that derives its evidence.
            const dispatcher = Reifier.settledType(reader.resolvedTypeIn(frame, param.dispatcher_ty));
            const selected = Reifier.receiverMethod(dispatcher, reader.names.methodNameText(param.method)) orelse continue;
            switch (selected.kind) {
                .procedure => |procedure| if (try self.derivedReaches(dispatcher.reader, procedure.template, .{ .receiver = dispatcher }, visited)) return true,
                .callable_binding => |binding| {
                    const computed = try dispatcher.reader.computedMethod(binding) orelse continue;
                    if ((try computed.reader.codeInventories()).inventoryOf(computed.template) != null) return true;
                },
                .local_proc, .structural => {},
            }
        }
        return false;
    }

    /// Whether a platform requirement's app binding that computes a function
    /// (not an exact alias) has an inventory, or null for any other binding.
    /// It never has one (design.md "Code Instance Tables"): the binding does
    /// not generalize, its type is the requirement's, and the only variables
    /// a requirement leaves free are tag rows written `..`, which close when
    /// the app module finishes checking. So its root has no variables and its
    /// entry wrapper has no inventory.
    fn computedRequirementInventory(self: *TableBuilder, requirement: *const RequirementUse) Allocator.Error!?bool {
        const reifier = self.reifier;
        const id = switch (reifier.procedure_bindings.get(requirement.binding.binding).body) {
            .callable_eval_template => |id| id,
            .direct_template, .checked_error => return null,
        };
        const template = reifier.callable_eval_templates.templates[@backingInt(id)];
        if (template.forwarded_lookup != null) return null;
        if (std.debug.runtime_safety) {
            const wrapper = reifier.entry_wrappers.lookupByRoot(template.root) orelse
                invariant("a binding that computes a function has no entry wrapper");
            const wrapper_template = reifier.procedure_templates.templates.items[@backingInt(wrapper.template.template)];
            if ((try reifier.codeInventories()).inventoryOf(wrapper_template.template_id) != null) {
                invariant("a platform requirement's binding that computes a function has an inventory");
            }
        }
        return false;
    }

    /// Attach to each `literal_argument` root of a generic bound call whose
    /// edge is the closing use `edge` the bound entry it reads in the tables
    /// `table` reaches (design.md "Bound Instance Roots").
    fn attachRoots(self: *TableBuilder, roots: []const checked.CompileTimeRoot, edge: checked.LiteralEdge, table: u32) Allocator.Error!void {
        for (roots) |root| {
            const argument = root.literal_argument orelse continue;
            if (argument.site.kind != .bound_call) continue;
            if (edge == .literal) invariant("a closing edge is no literal");
            if (!std.meta.eql(argument.edge, edge)) continue;
            try self.root_bounds.append(self.gpa, .{ .root = root.id, .entry = try self.requirementEntry(table, argument.callee_requirement) });
        }
    }

    /// The bound entry that requirement `first` of table `first_table`'s
    /// template reads: the chain of forwarded requirements, through the
    /// forward entries of the tables and the local scopes of their
    /// templates, ends at a generic bound call's own requirement.
    fn requirementEntry(self: *TableBuilder, first_table: u32, first: u32) Allocator.Error!u32 {
        var table = first_table;
        var reader = self.readers.items[table] orelse invariant("a closing use with a table names a refused table");
        const templates = reader.procedure_templates;
        var requirements = templates.templateLiteralRequirements(&templates.templates.items[self.templates.items[table].template]);
        var index = first;
        while (true) {
            if (index >= requirements.len) invariant("a bound requirement chain names a requirement its scheme does not have");
            const requirement = requirements[index];
            index = requirement.callee_requirement;
            const inventories = try reader.codeInventories();
            const edge: CodeEdge = switch (requirement.edge) {
                .literal => {
                    const span = self.table_bounds.items[table];
                    for (self.bound_entries.items[span.start..][0..span.len], span.start..) |entry, at| {
                        if (@backingInt(inventories.bound_calls[entry.call].call) == requirement.site.node) return @intCast(at);
                    }
                    invariant("a table has no bound entry for a generic bound call of its template");
                },
                .use, .node => requirement.edge,
                .requirement => invariant("a scheme's requirement forwards through a platform requirement"),
                // A contract call is never at a template's variables
                // (`EdgeScan.record`), so no requirement forwards through it.
                .derivation_call => invariant("a bound requirement forwards through a contract call"),
            };
            if (inventories.forwardIndex(edge)) |forward| {
                const entry = self.entries.items[self.tables.items[table].start + forward];
                if (entry.kind != .table) invariant("a forward entry of a table holds no table");
                table = entry.value;
                reader = self.readers.items[table] orelse invariant("a forward entry of a closed table names a refused table");
                const callee = reader.procedure_templates;
                requirements = callee.templateLiteralRequirements(&callee.templates.items[self.templates.items[table].template]);
                continue;
            }
            // An edge to a generalized local function stays in the table of
            // the template whose body holds the function.
            const local_use = switch (edge) {
                .use => |use| use,
                .node, .requirement, .derivation_call, .literal => invariant("a bound requirement's evidence edge is no forward entry"),
            };
            const scope = localScopeOfEdge(reader, local_use) orelse
                invariant("a bound requirement's edge is neither a forward entry nor a local function's");
            requirements = reader.procedure_templates.scopeLiteralRequirements(scope);
        }
    }

    /// The first refusal among the tables `root` reaches, or null.
    fn firstRejection(self: *TableBuilder, root: u32) Allocator.Error!?Rejection {
        var seen: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer seen.deinit(self.gpa);
        var pending = std.ArrayList(u32).empty;
        defer pending.deinit(self.gpa);
        try pending.append(self.gpa, root);
        while (pending.pop()) |table| {
            if ((try seen.getOrPut(self.gpa, table)).found_existing) continue;
            if (self.rejections.items[table]) |rejection| return rejection;
            const span = self.tables.items[table];
            for (self.entries.items[span.start..][0..span.len]) |entry| {
                if (entry.kind == .table) try pending.append(self.gpa, entry.value);
            }
        }
        return null;
    }

    /// Describe the sites of each generic bound call of `template` at the
    /// instance `chain` reaches, in site order, into their `entries`, and
    /// record the call's input slots at that instance on table `table`
    /// (R7). Each site's first slot counts the slots of the call's earlier
    /// sites at this instance.
    fn bindInstance(
        self: *TableBuilder,
        chain: []const ChainStep,
        holder: *Reifier,
        template: canonical.CheckedProcedureTemplateId,
        table: u32,
        entries: []InstanceTables.TableEntry,
    ) Allocator.Error!void {
        const instances = try holder.codeInventories();
        const inventory = instances.inventoryOf(template) orelse invariant("a table names a template with no inventory");
        const inventory_entries = instances.inventoryEntries(inventory);
        var made = std.ArrayList(InstanceTables.BoundEntry).empty;
        defer made.deinit(self.gpa);
        var call_slots = std.ArrayList(SlotSource).empty;
        defer call_slots.deinit(self.gpa);
        var owned = std.ArrayList([]SlotSource).empty;
        defer {
            for (owned.items) |slots| freeSlotSources(self.gpa, slots);
            owned.deinit(self.gpa);
        }
        for (instances.inventoryBoundCalls(inventory), 0..) |call, offset| {
            call_slots.clearRetainingCapacity();
            const first_start: u32 = @intCast(self.first_slots.items.len);
            var first: u64 = 0;
            for (instances.boundCallSites(call)) |site_index| {
                const recipe = instances.recipes[inventory_entries[site_index].recipe];
                const outcome = try self.describe(chain, holder, inventory_entries[site_index].node, recipe, first);
                const reads = try self.walk.takeReads();
                defer self.gpa.free(reads);
                const slots = self.walk.takeSlots();
                try owned.append(self.gpa, slots);
                switch (outcome) {
                    .reified => |node| {
                        const reads_start: u32 = @intCast(self.reads.items.len);
                        try self.reads.appendSlice(self.gpa, reads);
                        entries[site_index] = .{
                            .kind = .node,
                            .value = @backingInt(node),
                            .reads = .{ .start = reads_start, .len = @intCast(reads.len) },
                        };
                    },
                    .rejected => |rejection| {
                        self.rejections.items[table] = rejection;
                        return;
                    },
                }
                try self.first_slots.append(self.gpa, @intCast(first));
                first += slots.len;
                try call_slots.appendSlice(self.gpa, slots);
            }
            try made.append(self.gpa, .{
                .call = inventory.bound_calls.start + @as(u32, @intCast(offset)),
                .slots = try self.appendSlots(call_slots.items),
                .first_slots = .{ .start = first_start, .len = @as(u32, @intCast(self.first_slots.items.len)) - first_start },
            });
        }
        const start: u32 = @intCast(self.bound_entries.items.len);
        try self.bound_entries.appendSlice(self.gpa, made.items);
        self.table_bounds.items[table] = .{ .start = start, .len = @intCast(made.items.len) };
    }

    /// Describe the instance site `site` of `holder` at the instance `chain`
    /// reaches, in this module's store. `first_slot` is set for a site of a
    /// generic bound call: what the site reads at run time becomes input
    /// slots from that slot on.
    fn describe(self: *TableBuilder, chain: []const ChainStep, holder: *Reifier, site: ExprId, recipe: Inventories.Recipe, first_slot: ?u64) Allocator.Error!Outcome {
        const walk = self.walk;
        const inventories = try holder.codeInventories();
        walk.beginSite(recipe.view, false, self.reifier);
        if (first_slot) |first| {
            // Only the holder's run-time names are the call's inputs.
            walk.inputs = .{ .reader = holder, .call_leaves = inventories.boundCallLeaves(recipe.bound) };
            walk.useCaptureReads(try captureReads(self.gpa, holder, site));
            walk.first_slot = first;
        }
        try walk.startSite();
        var saved = SavedStates{ .gpa = self.gpa };
        defer saved.restore();
        const est = self.establish(chain, &saved) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.Rejected => return .{ .rejected = walk.rejection.? },
            error.Diverged => invariant("a divergence escaped before any row was built"),
        };
        std.debug.assert(est.reader == holder);
        // The holder reads the site in the instance the chain fixed.
        try saved.set(holder, est.frame, est.evidence, est.key);
        walk.instance = est.key;
        defer walk.instance = null;
        if (recipe.translator) |translator| try walk.useCut(holder, translator);
        const region = recipe.region;
        const root_reader = if (recipe.root_module == Inventories.none)
            holder
        else
            try walk.reader(walk.foreign.findModule(&inventories.modules[recipe.root_module].bytes) orelse
                invariant("a recipe's root module is in reach of every module that reaches the recipe"));
        walk.body = holder;
        try holder.relateSelectedTargets();
        try root_reader.relateSelectedTargets();
        const scheme: ?Reifier.Scheme = if (recipe.scheme_root) |root| .{
            .vars = inventories.recipeSchemeVars(recipe),
            .root = root,
        } else null;
        const root_body: ExprId = recipe.root_body;
        switch (recipe.kind) {
            .inline_lambda => return root_reader.outcomeOf(root_reader.rootSite(root_body, .{
                .scheme = null,
                .in_block = true,
                .caller = holder,
                .fixed = recipe.fn_ty,
                .region = region,
                .enclosing = .{ .frame = est.frame, .key = est.key, .evidence = est.evidence },
            }), region),
            .named_function => return root_reader.outcomeOf(root_reader.rootSite(root_body, .{
                .scheme = scheme,
                .in_block = recipe.in_block,
                .caller = holder,
                .fixed = recipe.fn_ty,
                .use = recipe.use,
                .region = region,
            }), region),
            // The proxy's type in the instance the chain fixed (Q8, D6).
            .type_id => {
                const bits = holder.typeIdIdentity(root_body) orelse return .{ .rejected = .{
                    .kind = .type_id_not_nominal,
                    .region = region,
                    .module = holder.rejectionModule(),
                    .detail = "",
                } };
                const store = walk.constStore();
                return .{ .reified = try store.append(.{ .record = &.{try store.append(.{ .scalar = .{ .u128 = bits } })} }) };
            },
            .ty_of => return holder.tyOfProxy(root_body, region),
            // A value site of a generic bound call is its input slot. Any
            // other value site is a literal at this instance.
            .value => {
                walk.value_literal = first_slot == null;
                return root_reader.outcomeOf(root_reader.valueRow(root_body, .{
                    .scheme = null,
                    .in_block = true,
                    .caller = holder,
                    .fixed = recipe.fn_ty,
                    .region = region,
                    .enclosing = .{ .frame = est.frame, .key = est.key, .evidence = est.evidence },
                }, first_slot != null), region);
            },
            .template_call => {
                var values = std.ArrayList(Reifier.TemplateArg).empty;
                defer values.deinit(self.gpa);
                defer holder.releaseTemplateArgs(values.items);
                if (try holder.reifyConstants(inventories.recipeArgs(recipe), &values, self.gpa)) |rejection| return .{ .rejected = rejection };
                const use = recipe.use orelse invariant("a template-call recipe names the template call's callee");
                return root_reader.outcomeOf(root_reader.templateSite(root_body, .{
                    .scheme = scheme.?,
                    .caller = holder,
                    .fixed = holder.bodies.expr(use).ty,
                    .use = use,
                }, values.items, region), region);
            },
        }
    }

    /// The table half of the closing uses built: `root_bounds` sorted by
    /// root. Takes the builder's lists.
    fn finish(self: *TableBuilder) Allocator.Error!InstanceTables {
        const gpa = self.gpa;
        std.mem.sort(InstanceTables.RootBound, self.root_bounds.items, {}, rootBoundLessThan);
        var result: InstanceTables = .{};
        errdefer result.deinit(gpa);
        result.tables = try self.tables.toOwnedSlice(gpa);
        result.table_templates = try self.templates.toOwnedSlice(gpa);
        result.table_entries = try self.entries.toOwnedSlice(gpa);
        result.reads = try self.reads.toOwnedSlice(gpa);
        result.table_bounds = try self.table_bounds.toOwnedSlice(gpa);
        result.bound_entries = try self.bound_entries.toOwnedSlice(gpa);
        result.slots = try self.slots.toOwnedSlice(gpa);
        result.slot_steps = try self.slot_steps.toOwnedSlice(gpa);
        result.slot_shapes = try self.slot_shapes.toOwnedSlice(gpa);
        result.first_slots = try self.first_slots.toOwnedSlice(gpa);
        result.root_bounds = try self.root_bounds.toOwnedSlice(gpa);
        result.implicit_instances = try self.implicit_instances.toOwnedSlice(gpa);
        result.owner_terms = try self.owner_terms.toOwnedSlice(gpa);
        result.owner_bindings = try self.owner_bindings.toOwnedSlice(gpa);
        result.owner_members = try self.owner_members.toOwnedSlice(gpa);
        result.owner_member_terms = try self.owner_member_terms.toOwnedSlice(gpa);
        result.owner_modules = try self.owner_modules.toOwnedSlice(gpa);
        return result;
    }
};

/// The template whose checked body is `body`, in `reader`'s module.
fn templateOfBody(reader: *Reifier, body: ExprId) ?canonical.CheckedProcedureTemplateId {
    for (reader.procedure_templates.templates.items) |template| {
        const root_expr = switch (template.body) {
            .checked_body => |root_expr| root_expr,
            .intrinsic_wrapper, .entry_wrapper, .unimplemented => continue,
        };
        if (root_expr == body) return template.template_id;
    }
    // A constant's evaluation runs its entry template, which has no checked
    // body of its own (Q16), and so does a binding that computes a function.
    for (reader.const_templates.templates.items) |template| switch (template.state) {
        .eval_template => |eval| if (reader.const_bodies.get(eval.body).body_expr == body) return eval.entry_template.template,
        .stored_const, .reserved, .unimplemented => {},
    };
    for (reader.callable_eval_templates.templates) |template| {
        if (template.forwarded_lookup != null or template.body != body) continue;
        const wrapper = reader.entry_wrappers.lookupByRoot(template.root) orelse
            invariant("a binding that computes a function has no entry wrapper");
        return wrapper.template.template;
    }
    return null;
}

/// The call a site is an argument of, whose translator declares the
/// site's cut, or null.
fn translatorCall(reifier: *const Reifier, site: CodeSiteRecord) ?ExprId {
    if (site.translator == CodeSiteRecord.no_translator) return null;
    const call: ExprId = @fromBackingInt(site.translator);
    // A call no body reaches is one checking rejected, and the build
    // already stops at its error.
    if (!reifier.bodies.index().reachesExpr(call)) return null;
    return call;
}

/// The cut of `site`, from the translator its call names (I14).
fn useSiteCut(walk: *Walk, reifier: *Reifier, site: CodeSiteRecord) Allocator.Error!void {
    const call = translatorCall(reifier, site) orelse return;
    try walk.useCut(reifier, call);
}

// The walk of one site, by its kind.
fn walkSite(
    gpa: Allocator,
    walk: *Walk,
    reifier: *Reifier,
    site: CodeSiteRecord,
    site_expr: ExprId,
    region: base.Region,
    call_args: *std.ArrayList(ExprId),
    call_values: *std.ArrayList(Reifier.TemplateArg),
) Allocator.Error!Outcome {
    return switch (site.kind) {
        .named_function => try reifyNamedSite(walk, reifier, site, region),
        // The lambda is the root, and the site is where it is written, so
        // the site node is what the walk reads, and the `f` beside it is
        // the type to read it at.
        .inline_lambda => try reifier.reifyLambda(site_expr, .{
            .scheme = null,
            .in_block = true,
            .caller = reifier,
            .fixed = siteFnType(reifier, site),
            .region = region,
        }),
        .template_call => try reifyTemplateSite(
            gpa,
            walk,
            reifier,
            site.node_idx,
            region,
            call_args,
            call_values,
        ),
        .value => try reifier.reifyValue(site_expr, .{
            .scheme = null,
            .in_block = true,
            .caller = reifier,
            .fixed = siteFnType(reifier, site),
            .region = region,
        }, site.bound_call != CodeSiteRecord.no_bound_call),
        .template, .template_callee => unreachable, // the caller skips template and template_callee sites
    };
}

/// Whether the normalized root row `root` delivers a data literal: a tree of
/// `lit`, `record`, `tuple`, `list`, `tag` and `wrap` nodes (R12).
fn rootDeliversDataLiteral(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!bool {
    const body = store.region(store.row(root).body);
    if (body.end.kind != .value or body.end.refs.len != 1) return false;
    var pending = std.ArrayList(ir.Ref).empty;
    defer pending.deinit(gpa);
    try pending.appendSlice(gpa, store.refSlice(body.end.refs));
    while (pending.pop()) |ref| {
        if (ref.kind != .node) return false;
        const node = store.node(ref.nodeId());
        switch (node.op) {
            .lit => {},
            .record, .tuple, .list, .tag, .wrap => try pending.appendSlice(gpa, store.refSlice(node.args)),
            .crash, .derived, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return false,
        }
    }
    return true;
}

fn freeSlotSources(gpa: Allocator, slots: []SlotSource) void {
    for (slots) |slot| {
        gpa.free(slot.steps);
        gpa.free(slot.shape);
    }
    gpa.free(slots);
}

/// The table half of a module's instance tables (D1): the table of each
/// closing use, built by the description step, and the bound entries of
/// each generic bound call a table binds. The description step commits it
/// into the module's `CodeOutput`.
///
/// | Slice | One entry per | Holds |
/// |---|---|---|
/// | `tables` | table, in build order | its span of `table_entries` |
/// | `table_templates` | table | the template whose inventory it serves |
/// | `table_entries` | inventory entry of a table | a description, a refusal, or the table of a forward use |
/// | `reads` | literal root a description reads | the read |
/// | `table_bounds` | table | its span of `bound_entries` |
/// | `bound_entries` | generic bound call of a table's template | its slots and each site's first slot |
/// | `slots`, `slot_steps`, `slot_shapes`, `first_slots` | slot of a bound entry | its leaf, projections, shape, and first slot |
/// | `root_bounds` | `literal_argument` root of a generic bound call, ascending by root | its bound entry |
/// | `implicit_instances` | table of a descriptor method at an owner type (Q17), in build order | the method, the owner, the table |
/// | `owner_terms`, `owner_bindings`, `owner_modules` | owner type of an implicit instance | a type of a module's store and what its variables stand for |
/// | `owner_members`, `owner_member_terms` | field or tag of a row term | its label, kind and terms |
pub const InstanceTables = struct {
    pub const Span = extern struct { start: u32 = 0, len: u32 = 0 };
    pub const none: u32 = std.math.maxInt(u32);

    pub const BoundEntry = extern struct {
        /// The generic bound call's index in its inventory's `bound_calls`.
        call: u32,
        slots: Span,
        first_slots: Span,
    };
    pub const RootBound = extern struct {
        root: checked.ComptimeRootId,
        entry: u32,
    };
    pub const TableTemplate = extern struct {
        module: checked.CheckedModuleArtifactKey,
        template: u32,
    };
    /// `node`: a description (`value` a `ConstNodeId`); `table`: the table
    /// of a forward use (`value` a table index). A table with a refused
    /// entry refuses its use, so no entry is refused.
    pub const TableEntryKind = enum(u32) { node, table };
    pub const TableEntry = extern struct {
        kind: TableEntryKind,
        value: u32,
        reads: Span,
    };

    /// A table of a descriptor method at an owner type (Q17): the method,
    /// the owner (an `owner_terms` index), and the table. One per table.
    pub const ImplicitInstance = extern struct {
        method: DescriptorMethod,
        owner: u32,
        table: u32,
    };
    /// `type`: `ty` with its `bindings`. `record_rest` and `tag_rest`: the
    /// rest of a row a row variable stands for, as its `members`; `ty` is
    /// the whole row the use matched, and `bindings` is empty.
    pub const OwnerTermKind = enum(u32) { type, record_rest, tag_rest };
    /// A type of the store of `owner_modules[module]`, with what each of
    /// its variables a frame fixed stands for: a span of `owner_bindings`.
    /// A row term is a span of `owner_members` instead.
    pub const OwnerTerm = extern struct {
        module: u32,
        kind: OwnerTermKind = .type,
        ty: CheckedTypeId,
        bindings: Span,
        members: Span = .{},
    };
    /// A field or a tag of a row term: its label in the store of
    /// `owner_modules[module]`, the field's kind, and a span of
    /// `owner_member_terms` (one term for a field, one per payload for a
    /// tag).
    pub const OwnerMember = extern struct {
        module: u32,
        label: u32,
        kind: checked.CheckedFieldKind = .{},
        terms: Span,
    };
    pub const OwnerBinding = extern struct {
        variable: CheckedTypeId,
        term: u32,
    };

    tables: []const Span = &.{},
    table_templates: []const TableTemplate = &.{},
    table_entries: []const TableEntry = &.{},
    reads: []const checked.CheckedCodeRead = &.{},
    table_bounds: []const Span = &.{},
    bound_entries: []const BoundEntry = &.{},
    slots: []const checked.CheckedCodeSlot = &.{},
    slot_steps: []const checked.CheckedCodeSlotStep = &.{},
    slot_shapes: []const u32 = &.{},
    first_slots: []const u32 = &.{},
    root_bounds: []const RootBound = &.{},
    implicit_instances: []const ImplicitInstance = &.{},
    owner_terms: []const OwnerTerm = &.{},
    owner_bindings: []const OwnerBinding = &.{},
    owner_members: []const OwnerMember = &.{},
    owner_member_terms: []const u32 = &.{},
    owner_modules: []const checked.CheckedModuleArtifactKey = &.{},

    pub fn deinit(self: *InstanceTables, gpa: Allocator) void {
        gpa.free(self.implicit_instances);
        gpa.free(self.owner_terms);
        gpa.free(self.owner_bindings);
        gpa.free(self.owner_members);
        gpa.free(self.owner_member_terms);
        gpa.free(self.owner_modules);
        gpa.free(self.tables);
        gpa.free(self.table_templates);
        gpa.free(self.table_entries);
        gpa.free(self.reads);
        gpa.free(self.table_bounds);
        gpa.free(self.bound_entries);
        gpa.free(self.slots);
        gpa.free(self.slot_steps);
        gpa.free(self.slot_shapes);
        gpa.free(self.first_slots);
        gpa.free(self.root_bounds);
        self.* = .{};
    }
};

/// A closing edge a table serves: a written use (a `for` loop's `iter` use
/// by the loop's body) or a platform requirement, and its table.
pub const ClosedEdge = struct { edge: CodeEdge, table: u32 };

/// The closing uses of one module, which the description step commits into
/// its `CodeOutput` and whose refusals it reports.
pub const ClosedUses = struct {
    tables: InstanceTables = .{},
    /// Ascending by `CodeEdgeKey`.
    edges: []ClosedEdge = &.{},
    /// In the order the uses were closed: written uses in node order, then
    /// requirements by requires index.
    refused: []RefusedUse = &.{},
    /// The type occurrences of descriptor methods refused (Q17), in body
    /// order.
    refused_implicits: []RefusedImplicit = &.{},
    /// Whether each of `tables.implicit_instances` is refused.
    implicit_refused: []bool = &.{},

    pub fn deinit(self: *ClosedUses, gpa: Allocator) void {
        self.tables.deinit(gpa);
        gpa.free(self.edges);
        gpa.free(self.refused);
        gpa.free(self.refused_implicits);
        gpa.free(self.implicit_refused);
        self.* = .{};
    }
};

/// What the description step of one module reads besides the module's
/// checked data: the module's compile-time roots, and the closing uses of
/// the platform requirements an app satisfies (design.md "Code Instance
/// Tables").
pub const DescribeInputs = struct {
    module: ModuleInputs,
    /// A closing use attaches its bound entries to the `literal_argument`
    /// roots of generic bound calls whose edge it is (design.md "Bound
    /// Instance Roots").
    roots: []const checked.CompileTimeRoot = &.{},
    /// Each successful function requirement of the platform this app
    /// module satisfies (`checked_artifact.platformRequirementClosingUses`).
    requirement_uses: []const RequirementUse = &.{},
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
    site: CodeSiteRecord,
    region: base.Region,
) Allocator.Error!Outcome {
    const root = switch (try namedRoot(walk, reifier, site.node_idx, region)) {
        .root => |root| root,
        .rejected => |rejection| return .{ .rejected = rejection },
    };
    return root.reader.reifyLambda(root.body, .{
        .scheme = root.scheme,
        .in_block = root.in_block,
        .caller = reifier,
        .fixed = siteFnType(reifier, site),
        .use = root.use,
        .region = region,
    });
}

/// The lambda a named site describes, and how the site fixes it: the reader
/// of the module that defines it, what it quantifies over, whether it reads
/// the block around it, and the site's lookup.
const NamedRoot = struct {
    reader: *Reifier,
    body: ExprId,
    scheme: ?Reifier.Scheme,
    in_block: bool,
    use: ?ExprId,
};

/// Where the name at a named site leads, or the reason it leads nowhere the
/// walk can read.
fn namedRoot(
    walk: *Walk,
    reifier: *Reifier,
    node_idx: u32,
    region: base.Region,
) Allocator.Error!union(enum) { root: NamedRoot, rejected: Rejection } {
    const use: ExprId = @fromBackingInt(node_idx);

    // An intrinsic has no body, and the walk never asks for one.
    if (namesIntrinsic(walk, reifier, use)) {
        return .{ .rejected = .{
            .kind = .unsupported_expression,
            .region = region,
            .module = reifier.rejectionModule(),
            .detail = "an intrinsic, a function with no Roc body, named as the function to describe",
        } };
    }

    // An exact function alias, `same = add_one`, has no body of its own. The
    // checker recorded the lookup it forwards to, and the site describes the
    // procedure that lookup names.
    const aliased = aliasedProcedure(walk, reifier, use, region) catch |err| switch (err) {
        error.Rejected => return .{ .rejected = walk.rejection.? },
        error.OutOfMemory => |e| return e,
        error.Diverged => invariant("a divergence escaped before any row was built"),
    };
    if (aliased) |reached| {
        return .{ .root = .{
            .reader = reached.reader,
            .body = reached.body,
            .scheme = reached.reader.templateScheme(reached.template),
            .in_block = false,
            .use = null,
        } };
    }

    const data = reifier.env.store.getExpr(use);
    if (data == .e_lookup_external) {
        const external = data.e_lookup_external;
        const definition = walk.foreign.find(external.module_idx, external.target_node_idx) orelse
            return .{ .rejected = unreachableDefinition(reifier, region, "a function no module this one imports exports").rejected };
        const away = try walk.reader(definition.module);
        return .{ .root = .{
            .reader = away,
            .body = definition.body,
            .scheme = away.templateScheme(definition.template),
            .in_block = false,
            .use = use,
        } };
    }

    if (stagedDefinition(reifier, use)) |staged| {
        return .{ .root = .{
            .reader = reifier,
            .body = staged.body,
            .scheme = reifier.templateScheme(staged.template),
            .in_block = false,
            .use = use,
        } };
    }

    // A local function the checker promoted is a procedure of its own. It
    // captures nothing, so it describes the way a top-level definition does,
    // through its own template and scheme.
    if (promotedDefinition(reifier, use)) |promoted| {
        return .{ .root = .{
            .reader = reifier,
            .body = promoted.body,
            .scheme = reifier.templateScheme(promoted.template),
            .in_block = false,
            .use = use,
        } };
    }

    // Anything else the checker records here is a name a block binds to a
    // lambda. The lambda reads the block around it the way one written at the
    // site does, and describes at the site's `f` through the scheme the block
    // generalized it to.
    const lambda = try blockLambda(reifier, use) orelse
        return .{ .rejected = unreachableDefinition(reifier, region, "a function this module does not define").rejected };
    return .{ .root = .{
        .reader = reifier,
        .body = lambda,
        .scheme = reifier.localScheme(lambda),
        .in_block = true,
        .use = use,
    } };
}

/// The definition of this module whose pattern `pattern` is, or null.
fn definitionOfPattern(reifier: *const Reifier, pattern: PatternId) ?CIR.Def.Idx {
    const env = reifier.env;
    for (env.store.sliceDefs(env.all_defs)) |def_idx| {
        if (env.store.getDef(def_idx).pattern == pattern) return def_idx;
    }
    return null;
}

/// Whether the name `use` names an intrinsic: a definition of this module,
/// or one that checking resolved an external lookup to.
fn namesIntrinsic(walk: *Walk, reifier: *const Reifier, use: ExprId) bool {
    const data = reifier.env.store.getExpr(use);
    if (data == .e_lookup_local) {
        const def_idx = definitionOfPattern(reifier, data.e_lookup_local.pattern_idx) orelse return false;
        return Reifier.defIsIntrinsic(reifier.env, def_idx);
    }
    if (data == .e_lookup_external) {
        const foreign = walk.foreign;
        const target = foreign.resolve_lookup_target(foreign.context, use) orelse return false;
        return Reifier.defIsIntrinsic(target.env, target.def);
    }
    return false;
}

/// The procedure the name `use` reaches when the name is an exact function
/// alias, or null when it is not one.
///
/// A named site holds no lookup the walk reads, so the source name leads to
/// the binding: a top-level value's pattern names its procedure binding, and
/// the binding says whether it is an alias. A name of another module leads to
/// that module's export row the way a definition does.
fn aliasedProcedure(
    walk: *Walk,
    reifier: *Reifier,
    use: ExprId,
    region: base.Region,
) Reifier.Error!?Reifier.ReachedProcedure {
    const data = reifier.env.store.getExpr(use);
    if (data == .e_lookup_external) {
        const external = data.e_lookup_external;
        const alias = walk.foreign.findAlias(external.module_idx, external.target_node_idx) orelse return null;
        const away = try walk.reader(alias.module);
        return try away.forwardedProcedure(alias.lookup, region);
    }
    if (data != .e_lookup_local) return null;
    const pattern = data.e_lookup_local.pattern_idx;
    const entry = reifier.top_level_values.lookupByPattern(pattern) orelse return null;
    const binding = switch (entry.value) {
        .procedure_binding => |binding| binding,
        .const_ref => return null,
    };
    if (reifier.procedure_bindings.get(binding).body != .callable_eval_template) return null;
    return try reifier.reachedProcedure(
        .{ .top_level = .{ .artifact = reifier.artifact.digest(), .binding = binding } },
        reifier.binderOf(pattern),
        region,
    );
}

/// The checked lambda a block binds the name `use` to: the binder's
/// defining statement holds it.
fn blockLambda(reifier: *Reifier, use: ExprId) Allocator.Error!?ExprId {
    const data = reifier.env.store.getExpr(use);
    if (data != .e_lookup_local) return null;
    const binder = reifier.binderOf(data.e_lookup_local.pattern_idx) orelse return null;
    return reifier.blockLambdaOf(binder);
}

/// A call to a template, described with the call's arguments written into it.
fn reifyTemplateSite(
    gpa: Allocator,
    walk: *Walk,
    reifier: *Reifier,
    node_idx: u32,
    region: base.Region,
    args: *std.ArrayList(ExprId),
    values: *std.ArrayList(Reifier.TemplateArg),
) Allocator.Error!Outcome {
    const call = try templateCall(gpa, reifier, node_idx, args, walk.foreign) orelse
        return unreachableDefinition(reifier, region, "a template this module cannot read");
    defer reifier.releaseTemplateArgs(values.items);

    // The arguments are written where the call is, so the local walk describes
    // them whether or not the template itself lives here.
    if (try reifier.reifyConstants(call.args, values, gpa)) |rejection| {
        return .{ .rejected = rejection };
    }

    // The callee's checked type is the template's type at this call, which
    // fixes the template's quantified variables (Q15).
    const fixed: CheckedTypeId = reifier.bodies.expr(call.callee).ty;
    switch (call.template) {
        .here => |definition| return reifier.reifyTemplateCall(definition.body, .{
            .scheme = reifier.templateScheme(definition.template),
            .caller = reifier,
            .fixed = fixed,
            .use = call.callee,
        }, values.items, region),
        .away => |definition| {
            const away = try walk.reader(definition.module);
            return away.reifyTemplateCall(definition.body, .{
                .scheme = away.templateScheme(definition.template),
                .caller = reifier,
                .fixed = fixed,
                .use = call.callee,
            }, values.items, region);
        },
    }
}

fn unreachableDefinition(site: *const Reifier, region: base.Region, detail: []const u8) Outcome {
    return .{ .rejected = .{
        .kind = .unresolved_reference,
        .region = region,
        .module = site.rejectionModule(),
        .detail = detail,
    } };
}

/// One template call's pieces: the function called, and the arguments it fixes.
const TemplateCall = struct {
    /// Where the template's body and procedure template are read from.
    template: union(enum) { here: StagedDefinition, away: ForeignDefinition },
    /// The name the call calls.
    callee: ExprId,
    args: []const ExprId,
};

/// The template a call site names, with the call's arguments.
///
/// `args` is built in the caller's scratch list, which every site reuses.
fn templateCall(
    gpa: Allocator,
    reifier: *const Reifier,
    node_idx: u32,
    args: *std.ArrayList(ExprId),
    foreign: ForeignLookup,
) Allocator.Error!?TemplateCall {
    const store = &reifier.env.store;
    const data = store.getExpr(@fromBackingInt(node_idx));
    if (data != .e_call) return null;
    const call = data.e_call;

    const callee = store.getExpr(call.func);
    const template: @FieldType(TemplateCall, "template") = blk: {
        if (callee == .e_lookup_local) {
            const definition = stagedDefinition(reifier, call.func) orelse return null;
            break :blk .{ .here = definition };
        }
        if (callee == .e_lookup_external) {
            const external = callee.e_lookup_external;
            const definition = foreign.find(external.module_idx, external.target_node_idx) orelse return null;
            break :blk .{ .away = definition };
        }
        return null;
    };

    args.clearRetainingCapacity();
    try args.appendSlice(gpa, store.sliceExpr(call.args));
    return .{ .template = template, .callee = call.func, .args = args.items };
}

/// The checked lambda a staged site names in this module, and the procedure
/// template that says what the definition quantifies over.
///
/// Null where the site names something this module does not define as a
/// top-level procedure, which the site reports as a definition it cannot
/// reach.
const StagedDefinition = struct {
    body: ExprId,
    template: checked.CheckedProcedureTemplate,
};

/// The procedure of the promoted local function the name `use` binds,
/// through the template publication recorded for its pattern.
fn promotedDefinition(reifier: *const Reifier, use: ExprId) ?StagedDefinition {
    const data = reifier.env.store.getExpr(use);
    if (data != .e_lookup_local) return null;
    const ref = reifier.procedure_templates.lookupPromotedByPattern(data.e_lookup_local.pattern_idx) orelse return null;
    const template = reifier.procedure_templates.get(ref.template);
    const body = switch (template.body) {
        .checked_body => |root_expr| root_expr,
        .intrinsic_wrapper, .entry_wrapper, .unimplemented => return null,
    };
    return .{ .body = body, .template = template };
}

/// The top-level procedure of this module the name `use` names.
fn stagedDefinition(reifier: *const Reifier, use: ExprId) ?StagedDefinition {
    const data = reifier.env.store.getExpr(use);
    if (data != .e_lookup_local) return null;
    const def_idx = definitionOfPattern(reifier, data.e_lookup_local.pattern_idx) orelse return null;
    const ref = reifier.procedure_templates.lookupByDef(def_idx) orelse return null;
    return .{ .body = reifier.env.store.getDef(def_idx).expr, .template = reifier.procedure_templates.get(ref.template) };
}

test "the reifier's walk compiles" {
    // `reifyLambda` reaches every arm of the walk, so referencing it forces
    // analysis of the whole reifier without a checked artifact to run on.
    _ = &Reifier.init;
    _ = &Reifier.deinit;
    _ = &Reifier.reifyLambda;
}
