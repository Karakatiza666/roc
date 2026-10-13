//! The rule table (I13).
//!
//! Every smart-constructor rule is one row: the op at its root, the patterns
//! of its arguments, its side conditions and its result. The builder's
//! dispatch, the knockout switch, the rule-set fingerprint and the derivation
//! tool all read this one table, so no rule exists outside it.

const std = @import("std");
const ir = @import("../ir.zig");
const prims = @import("../prims.zig");

const Op = ir.Op;

/// A pattern variable, numbered from 0 within one rule.
pub const Var = u8;

/// Which builtin module a prim pattern accepts.
pub const OwnerPat = union(enum) {
    /// Exactly this owner.
    fixed: prims.Owner,
    /// Any owner, bound to owner variable `k` on first use and compared after.
    bind: u8,
};

/// A pattern over the argument structure of a prospective node.
pub const Pat = union(enum) {
    /// Any value; binds pattern variable `k`, or compares with its binding.
    any: Var,
    /// A `Lit` of type `Bool` with this value.
    lit_bool: bool,
    /// An integer `Lit` of this value, read in its own type's signedness.
    lit_int: i64,
    /// A `Prim` node of this method and owner over these argument patterns.
    prim: struct { method: prims.Method, owner: OwnerPat, args: []const Pat },
    /// A node of this op over these argument patterns, whose payload is not
    /// constrained. Only ops without regions.
    op: struct { op: Op, args: []const Pat },
    /// A construction of `op` (`record`, `tuple`, `tag`) whose component at
    /// the root's position binds variable `bind`. The position is the root's
    /// payload for `field` and `index`, and the root's `aux[0]` for `payload`,
    /// whose tag must equal the construction's.
    component: struct { op: Op, bind: Var },
    /// A single-output `Switch` on a `Bool` over the scrutinee pattern, with
    /// its `False` arm first.
    bool_switch: struct { scrutinee: *const Pat, arms: [2]Arm },
    /// An `And` or `Or` whose operands, the first and then each operand
    /// region, match `operands` in order.
    connective: struct { op: Op, operands: []const OperandPat },
    /// A single-output `Switch` on a scrutinee of any type, whose arms all
    /// compute one value, compared structurally; binds region variable
    /// `region` to its first arm. Only a `switch_` root's pattern.
    same_arms: struct { scrutinee: *const Pat, region: RegionVar },
    /// A single-output `Switch` on a `Tag` construction; binds region
    /// variable `k` to the arm the tag selects. Only a `switch_` root's pattern.
    tag_arm: RegionVar,
    /// A run of zero or more operands of an associative builtin's chain;
    /// binds sequence variable `k`. Only in the arguments of a `prim` root or
    /// a `prim` pattern of an associative builtin (N15a). A rule names each
    /// sequence variable once, and the matcher tries the shortest run first.
    rest: SeqVar,
    /// The literal that is the identity of the `prim` root's builtin at its
    /// type (`prims.identityInt`). Only in a `prim` root's arguments.
    identity,
    /// The literal that absorbs the `prim` root's builtin at its type
    /// (`prims.absorbingInt`); binds pattern variable `k`. Only in a `prim`
    /// root's arguments.
    absorbing: Var,
    /// A single-output literal switch with one key, without joins: the
    /// scrutinee, whose integer type binds `owner`, the key's literal, and
    /// the keyed arm and then the default arm. The key's variable is a
    /// literal by the switch's form.
    lit_switch: struct { scrutinee: *const Pat, owner: OwnerPat, key: *const Pat, arms: [2]Arm },
};

/// A region variable, numbered from 0 within one rule, apart from pattern variables.
pub const RegionVar = u8;

/// A sequence variable, numbered from 0 within one rule, apart from pattern
/// and region variables. It binds a run of an `And` or `Or`'s operands.
pub const SeqVar = u8;

/// A pattern over one arm of a `Bool` switch, or over one operand of an `And` or `Or`.
pub const Arm = union(enum) {
    /// An arm whose value is this `Bool` literal.
    lit: bool,
    /// Any arm; binds region variable `k`. A second occurrence of `k` matches
    /// an arm that computes the same value, compared structurally. The first
    /// operand of an `And` or `Or` is not a region, so it never matches.
    region: RegionVar,
    /// An arm whose value this pattern matches.
    value: *const Pat,
};

/// One element of an `And` or `Or` pattern.
pub const OperandPat = union(enum) {
    /// One operand.
    arm: Arm,
    /// A run of zero or more operands; binds sequence variable `k`. A rule
    /// names each sequence variable once, and the matcher tries the shortest
    /// run first.
    rest: SeqVar,
};

/// A result template.
pub const Tmpl = union(enum) {
    /// The value bound to a pattern variable.
    var_: Var,
    /// A `Prim` of this method whose owner is `owner`, built over the templates.
    prim: struct { method: prims.Method, owner: OwnerPat, args: []const Tmpl },
    /// A single-output `Switch` on a `Bool` over the arms in the order given,
    /// `False` first.
    bool_switch: struct { scrutinee: *const Tmpl, arms: [2]ArmTmpl },
    /// `And` of the operands in order.
    and_: []const OperandTmpl,
    /// `Or` of the operands in order.
    or_: []const OperandTmpl,
    /// The value region variable `k` delivers, built where the result is.
    region_value: RegionVar,
    /// A `Bool` literal.
    lit_bool: bool,
    /// An integer literal of owner `owner`'s integer type.
    lit_int: struct { value: i64, owner: OwnerPat },
    /// The root's builtin evaluated over its literal operands, as a literal
    /// of the root's type. Only a row with the `folds` condition uses it.
    folded,
    /// The operands sequence variable `k` bound, in order. Only in the
    /// arguments of a `prim` template of an associative builtin, which over
    /// one operand is that operand, as a one-operand `And` is (N15a).
    rest: SeqVar,
    /// The negation of the template's value, built with the `Bool.not`
    /// pushed to the leaves: a `Bool.not` dropped, an `And` or `Or` turned
    /// into the other over negated operands, an integer `is_lt` or `is_lte`
    /// flipped, and any other leaf under a new `Bool.not`. The builder does
    /// this itself, so the rows that use it terminate whatever else is on.
    negation: *const Tmpl,
    /// A single-output literal switch on `scrutinee` with one keyed arm, for
    /// the literal `key`, then the default arm. A bound arm is copied under
    /// the new switch's facts (N13n).
    lit_switch: struct { scrutinee: *const Tmpl, key: *const Tmpl, arms: [2]ArmTmpl },
};

/// An arm of a result switch.
pub const ArmTmpl = union(enum) {
    /// A bound arm. An arm of the node being built is reused; an arm that
    /// already belongs to a node is copied.
    region: RegionVar,
    /// A new arm that computes this template.
    value: *const Tmpl,
};

/// One element of an `And` or `Or` result. The first operand is built where
/// the result is, and each later one in a region of its own, so a bound
/// region that ends up first has its value built where the result is.
pub const OperandTmpl = union(enum) {
    /// This value.
    value: *const Tmpl,
    /// A bound region, reused or copied as `ArmTmpl.region` is.
    region: RegionVar,
    /// The operands sequence variable `k` bound, in order.
    rest: SeqVar,
    /// The operands sequence variable `k` bound, in order, each negated as
    /// `Tmpl.negation` negates.
    negated_rest: SeqVar,
};

/// The fixed condition language of `roc-reify-rule-derivation.md` 3.4.
pub const Cond = union(enum) {
    /// Owner variable `k` is a builtin integer type.
    int_owner: u8,
    /// Owner variable `k` is not a float type.
    not_float_owner: u8,
    /// Pattern variable `k` is a literal.
    is_lit: Var,
    /// Pattern variable `k` is speculatable.
    speculatable: Var,
    /// Pattern variable `k` is a nonzero literal.
    nonzero_lit: Var,
    /// Region variable `k` reads only values visible where the rule's root
    /// is built, so a copy of it can be built there.
    movable: RegionVar,
    /// Every region among the operands sequence variable `k` bound is movable.
    movable_rest: SeqVar,
    /// Every argument among the arguments sequence variable `k` bound is
    /// speculatable, so a result without them drops nothing that can fail.
    speculatable_rest: SeqVar,
    /// The `Bool` value pattern variable `k` bound is in the polarity a
    /// switch on it flips (normal-form 3.13, N13s): its negation, with the
    /// `Bool.not` pushed to the leaves, has fewer `Bool.not` leaves; or as
    /// many and fewer integer `is_lte` leaves; or as many of both and, at an
    /// `And` or `Or` root, an `And` root where it has an `Or`, and at a
    /// `Bool` switch root, a first leaf that is neither a `Bool.not` nor an
    /// integer `is_lte` where its first leaf is one. Leaves are what the
    /// operands of `And` and `Or` and the arms of `Bool` switches reach
    /// that is none of these.
    polarity_flips: Var,
    /// The root is a builtin whose every operand is a literal, and it
    /// evaluates there without failing (N13j, N13k).
    folds,
    /// Pattern variable `k` has the root's type. A `Wrap` names its nominal
    /// in its type, not through its operand, so `Wrap(Unwrap(x))` is `x`
    /// only where `x` is of that nominal.
    same_ty: Var,
    /// Pattern variable `k` is a single-output literal switch whose arms all
    /// end in a `Bool` value, which a negation passes into (N13t).
    lit_bool_switch: Var,
    /// Pattern variable `k` is not a literal (N15c).
    not_lit: Var,
};

/// Which algorithm writes a rule (`roc-reify-rule-derivation.md` 2.3).
/// An `evaluation` row computes its result with the builtin itself, so it
/// has no term form for the derivation tool to orient or pair.
pub const Tier = enum { first_order, context, binder, evaluation };

/// One row of the table.
pub const Rule = struct {
    /// The step id in the plan, such as `N13h`.
    step: []const u8,
    tier: Tier,
    root: Op,
    /// The root's argument patterns, positionally.
    args: []const Pat,
    /// For a `prim` root, the method and owner the root must have.
    root_prim: ?struct { method: prims.Method, owner: OwnerPat } = null,
    conds: []const Cond = &.{},
    result: Tmpl,
};

/// The rules, in dispatch order. Each rule's id is its index: the written
/// rows, then their literal-switch mirrors.
pub const rules = written ++ mirrors.of(&written);

const written = [_]Rule{
    // Constant folding comes first: a builtin over literals is its value,
    // whatever else would rewrite it. `root_prim` is null, so each row
    // matches every builtin of its arity.
    .{
        .step = "N13j",
        .tier = .evaluation,
        .root = .prim,
        .args = &.{.{ .any = 0 }},
        .conds = &.{ .{ .is_lit = 0 }, .folds },
        .result = .folded,
    },
    .{
        .step = "N13j",
        .tier = .evaluation,
        .root = .prim,
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .conds = &.{ .{ .is_lit = 0 }, .{ .is_lit = 1 }, .folds },
        .result = .folded,
    },
    .{
        .step = "N13a",
        .tier = .first_order,
        .root = .field,
        .args = &.{.{ .component = .{ .op = .record, .bind = 0 } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13a",
        .tier = .first_order,
        .root = .index,
        .args = &.{.{ .component = .{ .op = .tuple, .bind = 0 } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13a",
        .tier = .first_order,
        .root = .payload,
        .args = &.{.{ .component = .{ .op = .tag, .bind = 0 } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13b",
        .tier = .first_order,
        .root = .unwrap,
        .args = &.{.{ .op = .{ .op = .wrap, .args = &.{.{ .any = 0 }} } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13h",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .any = 0 }} } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13t",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .connective = .{ .op = .and_, .operands = &.{.{ .rest = 0 }} } }},
        .result = .{ .or_ = &.{.{ .negated_rest = 0 }} },
    },
    .{
        .step = "N13t",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .connective = .{ .op = .or_, .operands = &.{.{ .rest = 0 }} } }},
        .result = .{ .and_ = &.{.{ .negated_rest = 0 }} },
    },
    .{
        .step = "N13t",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .value = &.{ .negation = &.{ .region_value = 0 } } }, .{ .value = &.{ .negation = &.{ .region_value = 1 } } } } } },
    },
    // N13t into a literal switch with `Bool` arms, of any number of keys.
    .{
        .step = "N13t",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .any = 0 }},
        .conds = &.{.{ .lit_bool_switch = 0 }},
        .result = .{ .negation = &.{ .var_ = 0 } },
    },
    .{
        .step = "N13q",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }},
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N13q",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .not, .owner = .{ .fixed = .bool_ } },
        .args = &.{.{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }},
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N13q",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N1l",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_gt, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .result = .{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N1l",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_gte, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .result = .{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N13e",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .lit = false }, .{ .lit = true } } } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13f",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .lit = true }, .{ .lit = false } } } }},
        .result = .{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } },
    },
    .{
        .step = "N13g",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .same_arms = .{ .scrutinee = &.{ .any = 0 }, .region = 0 } }},
        .result = .{ .region_value = 0 },
    },
    .{
        .step = "N13c",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .tag_arm = 0 }},
        .result = .{ .region_value = 0 },
    },
    // N15c, literal half: a literal operand of integer `is_eq`, `plus` and
    // `times` goes last. `Str.is_eq` waits for string literals in the tool's
    // terms. It needs the condition "is not a literal", which the tool's
    // generalization does not try (`roc-reify-rule-derivation.md` 3.4), so it
    // is written by hand; the tool checks its pairs and orients it.
    .{
        .step = "N15c",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .conds = &.{ .{ .int_owner = 0 }, .{ .is_lit = 0 }, .{ .not_lit = 1 } },
        .result = .{ .prim = .{ .method = .is_eq, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N15c",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .plus, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .conds = &.{ .{ .int_owner = 0 }, .{ .is_lit = 0 }, .{ .not_lit = 1 } },
        .result = .{ .prim = .{ .method = .plus, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "N15c",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 1 } },
        .conds = &.{ .{ .int_owner = 0 }, .{ .is_lit = 0 }, .{ .not_lit = 1 } },
        .result = .{ .prim = .{ .method = .times, .owner = .{ .bind = 0 }, .args = &.{ .{ .var_ = 1 }, .{ .var_ = 0 } } } },
    },
    // N13n: a switch on an integer `x == Lit` is a literal switch on `x`.
    // N15c puts the literal last first. It needs the literal switch, a symbol
    // the tool does not choose (`roc-reify-rule-derivation.md` 2.3), so it is
    // written by hand; the tool checks its pairs and orients it.
    .{
        .step = "N13n",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .prim = .{ .method = .is_eq, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .conds = &.{ .{ .int_owner = 0 }, .{ .is_lit = 1 } },
        .result = .{ .lit_switch = .{ .scrutinee = &.{ .var_ = 0 }, .key = &.{ .var_ = 1 }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N13i",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .any = 0 }} } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N13s",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .conds = &.{.{ .polarity_flips = 0 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .negation = &.{ .var_ = 0 } }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N13o",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .lit = false }, .{ .region = 0 } } } }},
        .result = .{ .and_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .region = 0 } } },
    },
    .{
        .step = "N13o",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .lit = true } } } }},
        .result = .{ .or_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .region = 0 } } },
    },
    .{
        .step = "N13o",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .lit = false } } } }},
        .result = .{ .and_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N13o",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .lit = true }, .{ .region = 0 } } } }},
        .result = .{ .or_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } } } } } }},
        .conds = &.{.{ .movable = 1 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .and_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .value = &.{ .var_ = 1 } } } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } } }, .{ .region = 0 } } } }},
        .conds = &.{.{ .movable = 1 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .or_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .value = &.{ .var_ = 1 } } } }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } } }, .{ .region = 0 } } } }},
        .conds = &.{.{ .movable = 1 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .and_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .value = &.{ .var_ = 1 } } } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } } } } } }},
        .conds = &.{.{ .movable = 1 }},
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .or_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .value = &.{ .var_ = 1 } } } }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .value = &.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } } } } }},
        .result = .{ .or_ = &.{ .{ .value = &.{ .and_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .value = &.{ .or_ = &.{.{ .rest = 0 }} } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .region = 0 }, .{ .value = &.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } } } } }},
        .result = .{ .and_ = &.{ .{ .value = &.{ .or_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .value = &.{ .and_ = &.{.{ .rest = 0 }} } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } }, .{ .region = 0 } } } }},
        .result = .{ .and_ = &.{ .{ .value = &.{ .or_ = &.{ .{ .value = &.{ .var_ = 0 } }, .{ .value = &.{ .and_ = &.{.{ .rest = 0 }} } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } }, .{ .region = 0 } } } }},
        .result = .{ .or_ = &.{ .{ .value = &.{ .and_ = &.{ .{ .value = &.{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } } }, .{ .value = &.{ .or_ = &.{.{ .rest = 0 }} } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } } }, .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 2 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } } } } } }},
        .conds = &.{ .{ .movable = 0 }, .{ .movable = 1 } },
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .value = &.{ .var_ = 1 } }, .{ .value = &.{ .var_ = 2 } } } } }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 1 }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } } }, .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .any = 2 }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } } } } } }},
        .conds = &.{ .{ .movable = 0 }, .{ .movable = 1 } },
        .result = .{ .bool_switch = .{ .scrutinee = &.{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .value = &.{ .negation = &.{ .var_ = 1 } } }, .{ .value = &.{ .var_ = 2 } } } } }, .arms = .{ .{ .region = 1 }, .{ .region = 0 } } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } }, .{ .value = &.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 1 }, .{ .arm = .{ .region = 0 } } } } } } } } }},
        .result = .{ .and_ = &.{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .value = &.{ .and_ = &.{.{ .rest = 0 }} } }, .{ .value = &.{ .and_ = &.{.{ .rest = 1 }} } } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N7d",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .any = 0 }, .arms = .{ .{ .value = &.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .region = 0 } } } } } }, .{ .value = &.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 1 }, .{ .arm = .{ .region = 0 } } } } } } } } }},
        .result = .{ .or_ = &.{ .{ .value = &.{ .bool_switch = .{ .scrutinee = &.{ .var_ = 0 }, .arms = .{ .{ .value = &.{ .or_ = &.{.{ .rest = 0 }} } }, .{ .value = &.{ .or_ = &.{.{ .rest = 1 }} } } } } } }, .{ .region = 0 } } },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .and_,
        .args = &.{.{ .connective = .{ .op = .and_, .operands = &.{.{ .arm = .{ .value = &.{ .any = 0 } } }} } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .or_,
        .args = &.{.{ .connective = .{ .op = .or_, .operands = &.{.{ .arm = .{ .value = &.{ .any = 0 } } }} } }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .and_,
        .args = &.{.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .lit = false } }, .{ .rest = 1 } } } }},
        .result = .{ .lit_bool = false },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .or_,
        .args = &.{.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .lit = true } }, .{ .rest = 1 } } } }},
        .result = .{ .lit_bool = true },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .and_,
        .args = &.{.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .lit = true } }, .{ .rest = 1 } } } }},
        .result = .{ .and_ = &.{ .{ .rest = 0 }, .{ .rest = 1 } } },
    },
    .{
        .step = "N13p",
        .tier = .first_order,
        .root = .or_,
        .args = &.{.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .lit = false } }, .{ .rest = 1 } } } }},
        .result = .{ .or_ = &.{ .{ .rest = 0 }, .{ .rest = 1 } } },
    },
    .{
        .step = "N15b",
        .tier = .first_order,
        .root = .and_,
        .args = &.{.{ .connective = .{ .op = .and_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .value = &.{ .connective = .{ .op = .and_, .operands = &.{.{ .rest = 1 }} } } } }, .{ .rest = 2 } } } }},
        .conds = &.{.{ .movable_rest = 1 }},
        .result = .{ .and_ = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } },
    },
    .{
        .step = "N15b",
        .tier = .first_order,
        .root = .or_,
        .args = &.{.{ .connective = .{ .op = .or_, .operands = &.{ .{ .rest = 0 }, .{ .arm = .{ .value = &.{ .connective = .{ .op = .or_, .operands = &.{.{ .rest = 1 }} } } } }, .{ .rest = 2 } } } }},
        .conds = &.{.{ .movable_rest = 1 }},
        .result = .{ .or_ = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } },
    },
    // A chain is one `Prim` whatever its grouping; order is kept, because none of these is commutative in the normal form.
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .plus_wrap, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .plus_wrap, .owner = .{ .bind = 0 }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .plus_wrap, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_xor, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .bitwise_xor, .owner = .{ .bind = 0 }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .bitwise_xor, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .concat, .owner = .{ .fixed = .str } },
        .args = &.{ .{ .rest = 0 }, .{ .prim = .{ .method = .concat, .owner = .{ .fixed = .str }, .args = &.{.{ .rest = 1 }} } }, .{ .rest = 2 } },
        .result = .{ .prim = .{ .method = .concat, .owner = .{ .fixed = .str }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 }, .{ .rest = 2 } } } },
    },
    // An identity operand drops out of a chain; a chain left with one operand is that operand.
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .plus_wrap, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .identity, .{ .rest = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .plus_wrap, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .identity, .{ .rest = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .identity, .{ .rest = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .identity, .{ .rest = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 } } } },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_xor, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .identity, .{ .rest = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .bitwise_xor, .owner = .{ .bind = 0 }, .args = &.{ .{ .rest = 0 }, .{ .rest = 1 } } } },
    },
    // An absorbing operand is the chain, where the operands it drops cannot fail.
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times_wrap, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .absorbing = 0 }, .{ .rest = 1 } },
        .conds = &.{ .{ .speculatable_rest = 0 }, .{ .speculatable_rest = 1 }, .{ .int_owner = 0 } },
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_and, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .absorbing = 0 }, .{ .rest = 1 } },
        .conds = &.{ .{ .speculatable_rest = 0 }, .{ .speculatable_rest = 1 }, .{ .int_owner = 0 } },
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "N15a",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .bitwise_or, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .rest = 0 }, .{ .absorbing = 0 }, .{ .rest = 1 } },
        .conds = &.{ .{ .speculatable_rest = 0 }, .{ .speculatable_rest = 1 }, .{ .int_owner = 0 } },
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T1.1",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 0 } },
        .conds = &.{ .{ .speculatable = 0 }, .{ .int_owner = 0 } },
        .result = .{ .lit_bool = true },
    },
    .{
        .step = "T1.2",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_lte, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 0 } },
        .conds = &.{ .{ .speculatable = 0 }, .{ .int_owner = 0 } },
        .result = .{ .lit_bool = true },
    },
    .{
        .step = "T1.3",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .any = 0 }, .{ .lit_bool = true } },
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T1.4",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .lit_bool = true }, .{ .any = 0 } },
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T1.5",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .any = 0 }, .{ .lit_bool = false } },
        .result = .{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } },
    },
    .{
        .step = "T1.6",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .lit_bool = false }, .{ .any = 0 } },
        .result = .{ .prim = .{ .method = .not, .owner = .{ .fixed = .bool_ }, .args = &.{.{ .var_ = 0 }} } },
    },
    .{
        .step = "T1.7",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_lt, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 0 } },
        .conds = &.{ .{ .speculatable = 0 }, .{ .int_owner = 0 } },
        .result = .{ .lit_bool = false },
    },
    .{
        .step = "T1.8",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .minus, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .lit_int = 0 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T1.10",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .plus, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .lit_int = 0 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T1.11",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .minus, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .any = 0 } },
        .conds = &.{ .{ .speculatable = 0 }, .{ .int_owner = 0 } },
        .result = .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } },
    },
    .{
        .step = "T2.1",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .lit_bool = false }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .result = .{ .region_value = 0 },
    },
    .{
        .step = "T2.2",
        .tier = .first_order,
        .root = .switch_,
        .args = &.{.{ .bool_switch = .{ .scrutinee = &.{ .lit_bool = true }, .arms = .{ .{ .region = 0 }, .{ .region = 1 } } } }},
        .result = .{ .region_value = 1 },
    },
    .{
        .step = "T3.1",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .any = 0 }, .{ .any = 0 } },
        .conds = &.{.{ .speculatable = 0 }},
        .result = .{ .lit_bool = true },
    },
    .{
        .step = "T3.6",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .{ .any = 1 } },
        .conds = &.{.{ .speculatable = 1 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T3.7",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .{ .any = 0 } },
        .conds = &.{.{ .speculatable = 0 }},
        .result = .{ .var_ = 1 },
    },
    .{
        .step = "T3.8",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .any = 0 }, .{ .prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ }, .args = &.{ .{ .any = 1 }, .{ .any = 0 } } } } },
        .conds = &.{.{ .speculatable = 0 }},
        .result = .{ .var_ = 1 },
    },
    .{
        .step = "T3.9",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .any = 0 }, .{ .prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } } },
        .conds = &.{.{ .speculatable = 0 }},
        .result = .{ .var_ = 1 },
    },
    .{
        .step = "T3.10",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .minus, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .any = 0 }, .{ .prim = .{ .method = .minus, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = 0 }, .{ .any = 0 } } } } },
        .result = .{ .prim = .{ .method = .plus, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .var_ = 0 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T3.11",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .plus, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .prim = .{ .method = .minus, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = 0 }, .{ .any = 0 } } } }, .{ .lit_int = 1 } },
        .result = .{ .prim = .{ .method = .minus, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = .{ .value = 1, .owner = .{ .fixed = .i64 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T4.1",
        .tier = .first_order,
        .root = .wrap,
        .args = &.{.{ .op = .{ .op = .unwrap, .args = &.{.{ .any = 0 }} } }},
        .conds = &.{.{ .same_ty = 0 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T5.1",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .lit_int = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T5.3",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .lit_int = 1 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .var_ = 0 },
    },
    .{
        .step = "T5.16",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .times, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .any = 0 }, .{ .lit_int = 0 } },
        .conds = &.{ .{ .speculatable = 0 }, .{ .int_owner = 0 } },
        .result = .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } },
    },
    .{
        .step = "T5.6",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .lit_int = 1 }, .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .any = 0 }, .{ .any = 0 } } } } },
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .var_ = 0 }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.7",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .lit_int = 0 }, .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 0 } } } } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.8",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .lit_int = 0 }, .{ .any = 0 } } } }, .{ .any = 0 } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.9",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 } },
        .args = &.{ .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .lit_int = 0 }, .{ .any = 0 } } } }, .{ .any = 1 } },
        .conds = &.{ .{ .nonzero_lit = 1 }, .{ .int_owner = 0 } },
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .bind = 0 }, .args = &.{ .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.10",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = 1 }, .{ .any = 0 } } } }, .{ .lit_int = -1 } },
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = .{ .value = -1, .owner = .{ .fixed = .i64 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.11",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .any = 0 }, .{ .any = 0 } } } }, .{ .any = 0 } },
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = .{ .value = 1, .owner = .{ .fixed = .i64 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T5.12",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 } },
        .args = &.{ .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = -1 }, .{ .any = 0 } } } }, .{ .lit_int = -1 } },
        .result = .{ .prim = .{ .method = .div_trunc, .owner = .{ .fixed = .i64 }, .args = &.{ .{ .lit_int = .{ .value = 1, .owner = .{ .fixed = .i64 } } }, .{ .var_ = 0 } } } },
    },
    .{
        .step = "T6.1",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 1 }, .{ .any = 0 } } } } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .lit_bool = false },
    },
    .{
        .step = "T6.2",
        .tier = .first_order,
        .root = .prim,
        .root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } },
        .args = &.{ .{ .prim = .{ .method = .is_lt, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 0 }, .{ .any = 1 } } } }, .{ .prim = .{ .method = .is_lte, .owner = .{ .bind = 0 }, .args = &.{ .{ .any = 1 }, .{ .any = 0 } } } } },
        .conds = &.{.{ .int_owner = 0 }},
        .result = .{ .lit_bool = false },
    },
};

/// A rule's id: its index in `rules`.
pub const RuleId = enum(u16) {
    _,

    /// The rule with this index.
    pub fn of(i: usize) RuleId {
        return @fromBackingInt(@intCast(i));
    }

    /// This rule's index.
    pub fn index(self: RuleId) usize {
        return @backingInt(self);
    }

    /// This rule's row.
    pub fn rule(self: RuleId) Rule {
        return rules[self.index()];
    }
};

/// The number of rules.
pub const count = rules.len;

/// The literal-switch mirrors (N13n). N13n writes `switch(is_eq(s, k), f, t)`
/// as the literal switch `switch_#1(s, k, t, f)`, so a row with a `Bool`
/// switch pattern on a variable `v` would never meet that switch once N13n
/// fired. Its mirror is the row composed with N13n's equation: the pattern
/// `switch(v, f, t)` becomes `switch_#1(s, k, t, f)` over fresh variables,
/// with a fresh integer owner, and the result reads `v` as `is_eq(s, k)`,
/// except that a result switch on `v` is N13n's literal switch.
/// Each is exact, because both equations are; the derivation tool orients
/// and pairs it as it does every row. One mirror is made for every nonempty
/// set of a row's switch patterns whose variable occurs once in the row's
/// patterns and in no condition. A mirror's step is its row's with `/N13n`.
const mirrors = struct {
    fn of(comptime rows: []const Rule) [countOf(rows)]Rule {
        @setEvalBranchQuota(2_000_000);
        var out: [countOf(rows)]Rule = undefined;
        var n: usize = 0;
        for (rows) |r| {
            const vs = eligible(r);
            for (1..@as(usize, 1) << @intCast(vs.len)) |mask| {
                var ms: [vs.len]Mirror = undefined;
                var m: usize = 0;
                for (vs, 0..) |v, i| if (mask & (@as(usize, 1) << @intCast(i)) != 0) {
                    ms[m] = .{ .v = v, .s = varCount(r) + 2 * m, .k = varCount(r) + 2 * m + 1, .o = ownerVarCount(r) + m };
                    m += 1;
                };
                out[n] = mirror(r, ms[0..m]);
                n += 1;
            }
        }
        return out;
    }

    const Mirror = struct { v: Var, s: Var, k: Var, o: u8 };

    fn countOf(comptime rows: []const Rule) usize {
        @setEvalBranchQuota(2_000_000);
        var n: usize = 0;
        for (rows) |r| n += (@as(usize, 1) << @intCast(eligible(r).len)) - 1;
        return n;
    }

    fn mirror(comptime r: Rule, comptime ms: []const Mirror) Rule {
        var args: [r.args.len]Pat = undefined;
        for (r.args, &args) |a, *o| o.* = pat(a, ms);
        var conds: [r.conds.len + ms.len]Cond = undefined;
        for (r.conds, 0..) |c, i| conds[i] = c;
        for (ms, 0..) |m, i| conds[r.conds.len + i] = .{ .int_owner = m.o };
        const final_args = args;
        const final_conds = conds;
        return .{ .step = r.step ++ "/N13n", .tier = r.tier, .root = r.root, .args = &final_args, .root_prim = r.root_prim, .conds = &final_conds, .result = tmpl(r.result, ms) };
    }

    // The variables of `r`'s switch patterns that a mirror can replace.
    fn eligible(comptime r: Rule) []const Var {
        if (r.tier != .first_order) return &.{};
        var out: []const Var = &.{};
        for (r.args) |a| out = out ++ switchVars(a);
        var kept: []const Var = &.{};
        for (out) |v| {
            var uses: u32 = 0;
            for (r.args) |a| uses += usesOf(a, v);
            const in_cond = for (r.conds) |c| switch (c) {
                .is_lit, .speculatable, .nonzero_lit, .polarity_flips, .same_ty, .lit_bool_switch, .not_lit => |k| if (k == v) break true,
                .int_owner, .not_float_owner, .movable, .movable_rest, .speculatable_rest, .folds => {},
            } else false;
            if (uses == 1 and !in_cond) kept = kept ++ .{v};
        }
        return kept;
    }

    fn switchVars(comptime p: Pat) []const Var {
        return switch (p) {
            .any, .lit_bool, .lit_int, .component, .tag_arm, .rest, .identity, .absorbing => &.{},
            .bool_switch => |bs| (if (bs.scrutinee.* == .any) &[_]Var{bs.scrutinee.any} else switchVars(bs.scrutinee.*)) ++ armSwitchVars(bs.arms[0]) ++ armSwitchVars(bs.arms[1]),
            .same_arms => |sa| switchVars(sa.scrutinee.*),
            .lit_switch => |ls| switchVars(ls.scrutinee.*) ++ armSwitchVars(ls.arms[0]) ++ armSwitchVars(ls.arms[1]),
            .prim => |pp| blk: {
                var out: []const Var = &.{};
                for (pp.args) |a| out = out ++ switchVars(a);
                break :blk out;
            },
            .op => |op| blk: {
                var out: []const Var = &.{};
                for (op.args) |a| out = out ++ switchVars(a);
                break :blk out;
            },
            .connective => |c| blk: {
                var out: []const Var = &.{};
                for (c.operands) |o| switch (o) {
                    .arm => |a| out = out ++ armSwitchVars(a),
                    .rest => {},
                };
                break :blk out;
            },
        };
    }

    fn armSwitchVars(comptime a: Arm) []const Var {
        return switch (a) {
            .lit, .region => &.{},
            .value => |p| switchVars(p.*),
        };
    }

    // How often pattern `p` binds or reads variable `v`.
    fn usesOf(comptime p: Pat, v: Var) u32 {
        return switch (p) {
            .any, .absorbing => |k| @intFromBool(k == v),
            .component => |c| @intFromBool(c.bind == v),
            .lit_bool, .lit_int, .tag_arm, .rest, .identity => 0,
            .bool_switch => |bs| usesOf(bs.scrutinee.*, v) + armUses(bs.arms[0], v) + armUses(bs.arms[1], v),
            .same_arms => |sa| usesOf(sa.scrutinee.*, v),
            .lit_switch => |ls| usesOf(ls.scrutinee.*, v) + usesOf(ls.key.*, v) + armUses(ls.arms[0], v) + armUses(ls.arms[1], v),
            .prim => |pp| blk: {
                var n: u32 = 0;
                for (pp.args) |a| n += usesOf(a, v);
                break :blk n;
            },
            .op => |op| blk: {
                var n: u32 = 0;
                for (op.args) |a| n += usesOf(a, v);
                break :blk n;
            },
            .connective => |c| blk: {
                var n: u32 = 0;
                for (c.operands) |o| switch (o) {
                    .arm => |a| n += armUses(a, v),
                    .rest => {},
                };
                break :blk n;
            },
        };
    }

    fn armUses(comptime a: Arm, v: Var) u32 {
        return switch (a) {
            .lit, .region => 0,
            .value => |p| usesOf(p.*, v),
        };
    }

    fn find(comptime ms: []const Mirror, v: Var) ?Mirror {
        for (ms) |m| if (m.v == v) return m;
        return null;
    }

    fn ptr(comptime T: type, comptime x: T) *const T {
        const c = x;
        return &c;
    }

    fn pat(comptime p: Pat, comptime ms: []const Mirror) Pat {
        return switch (p) {
            .any, .lit_bool, .lit_int, .component, .tag_arm, .rest, .identity, .absorbing => p,
            .bool_switch => |bs| if (bs.scrutinee.* == .any and find(ms, bs.scrutinee.any) != null) blk: {
                const m = find(ms, bs.scrutinee.any).?;
                // The `True` arm is the keyed one.
                break :blk .{ .lit_switch = .{ .scrutinee = ptr(Pat, .{ .any = m.s }), .owner = .{ .bind = m.o }, .key = ptr(Pat, .{ .any = m.k }), .arms = .{ arm(bs.arms[1], ms), arm(bs.arms[0], ms) } } };
            } else .{ .bool_switch = .{ .scrutinee = ptr(Pat, pat(bs.scrutinee.*, ms)), .arms = .{ arm(bs.arms[0], ms), arm(bs.arms[1], ms) } } },
            .same_arms => |sa| .{ .same_arms = .{ .scrutinee = ptr(Pat, pat(sa.scrutinee.*, ms)), .region = sa.region } },
            .lit_switch => |ls| .{ .lit_switch = .{ .scrutinee = ptr(Pat, pat(ls.scrutinee.*, ms)), .owner = ls.owner, .key = ls.key, .arms = .{ arm(ls.arms[0], ms), arm(ls.arms[1], ms) } } },
            .prim => |pp| blk: {
                var args: [pp.args.len]Pat = undefined;
                for (pp.args, &args) |a, *o| o.* = pat(a, ms);
                const final = args;
                break :blk .{ .prim = .{ .method = pp.method, .owner = pp.owner, .args = &final } };
            },
            .op => |op| blk: {
                var args: [op.args.len]Pat = undefined;
                for (op.args, &args) |a, *o| o.* = pat(a, ms);
                const final = args;
                break :blk .{ .op = .{ .op = op.op, .args = &final } };
            },
            .connective => |c| blk: {
                var ops: [c.operands.len]OperandPat = undefined;
                for (c.operands, &ops) |o, *q| q.* = switch (o) {
                    .arm => |a| .{ .arm = arm(a, ms) },
                    .rest => o,
                };
                const final = ops;
                break :blk .{ .connective = .{ .op = c.op, .operands = &final } };
            },
        };
    }

    fn arm(comptime a: Arm, comptime ms: []const Mirror) Arm {
        return switch (a) {
            .lit, .region => a,
            .value => |p| .{ .value = ptr(Pat, pat(p.*, ms)) },
        };
    }

    fn tmpl(comptime t: Tmpl, comptime ms: []const Mirror) Tmpl {
        return switch (t) {
            .var_ => |v| if (find(ms, v)) |m|
                .{ .prim = .{ .method = .is_eq, .owner = .{ .bind = m.o }, .args = ptr([2]Tmpl, .{ .{ .var_ = m.s }, .{ .var_ = m.k } }) } }
            else
                t,
            .region_value, .lit_bool, .lit_int, .folded, .rest => t,
            .prim => |pp| blk: {
                var args: [pp.args.len]Tmpl = undefined;
                for (pp.args, &args) |a, *o| o.* = tmpl(a, ms);
                const final = args;
                break :blk .{ .prim = .{ .method = pp.method, .owner = pp.owner, .args = &final } };
            },
            // A switch on `v` is N13n's literal switch, its `True` arm keyed.
            .bool_switch => |bs| if (bs.scrutinee.* == .var_ and find(ms, bs.scrutinee.var_) != null) blk: {
                const m = find(ms, bs.scrutinee.var_).?;
                break :blk .{ .lit_switch = .{ .scrutinee = ptr(Tmpl, .{ .var_ = m.s }), .key = ptr(Tmpl, .{ .var_ = m.k }), .arms = .{ armTmpl(bs.arms[1], ms), armTmpl(bs.arms[0], ms) } } };
            } else .{ .bool_switch = .{ .scrutinee = ptr(Tmpl, tmpl(bs.scrutinee.*, ms)), .arms = .{ armTmpl(bs.arms[0], ms), armTmpl(bs.arms[1], ms) } } },
            .lit_switch => |ls| .{ .lit_switch = .{ .scrutinee = ptr(Tmpl, tmpl(ls.scrutinee.*, ms)), .key = ls.key, .arms = .{ armTmpl(ls.arms[0], ms), armTmpl(ls.arms[1], ms) } } },
            .and_, .or_ => |ops| blk: {
                var out: [ops.len]OperandTmpl = undefined;
                for (ops, &out) |o, *q| q.* = switch (o) {
                    .value => |v| .{ .value = ptr(Tmpl, tmpl(v.*, ms)) },
                    .region, .rest, .negated_rest => o,
                };
                const final = out;
                break :blk if (t == .and_) .{ .and_ = &final } else .{ .or_ = &final };
            },
            .negation => |v| .{ .negation = ptr(Tmpl, tmpl(v.*, ms)) },
        };
    }

    fn armTmpl(comptime a: ArmTmpl, comptime ms: []const Mirror) ArmTmpl {
        return switch (a) {
            .region => a,
            .value => |v| .{ .value = ptr(Tmpl, tmpl(v.*, ms)) },
        };
    }
};

/// The number of pattern variables a rule binds.
pub fn varCount(rule: Rule) u8 {
    return argsCount(rule, .vars);
}

/// The number of region variables a rule binds.
pub fn regionVarCount(rule: Rule) u8 {
    return argsCount(rule, .regions);
}

/// The number of sequence variables a rule binds.
pub fn seqVarCount(rule: Rule) u8 {
    return argsCount(rule, .seqs);
}

/// The number of owner variables a rule binds.
pub fn ownerVarCount(rule: Rule) u8 {
    var n = argsCount(rule, .owners);
    if (rule.root_prim) |rp| n = @max(n, ownerPatCount(rp.owner));
    return n;
}

const Kind = enum { vars, regions, seqs, owners };

fn argsCount(rule: Rule, kind: Kind) u8 {
    var n: u8 = 0;
    for (rule.args) |p| n = @max(n, patCount(p, kind));
    return n;
}

// One more than the highest variable of `kind` that `p` binds.
fn patCount(p: Pat, kind: Kind) u8 {
    return switch (p) {
        .any => |k| if (kind == .vars) k + 1 else 0,
        .lit_bool, .lit_int => 0,
        .prim => |pp| blk: {
            var n: u8 = if (kind == .owners) ownerPatCount(pp.owner) else 0;
            for (pp.args) |a| n = @max(n, patCount(a, kind));
            break :blk n;
        },
        .op => |op| blk: {
            var n: u8 = 0;
            for (op.args) |a| n = @max(n, patCount(a, kind));
            break :blk n;
        },
        .component => |c| if (kind == .vars) c.bind + 1 else 0,
        .bool_switch => |bs| @max(patCount(bs.scrutinee.*, kind), armCount(bs.arms[0], kind), armCount(bs.arms[1], kind)),
        .connective => |c| blk: {
            var n: u8 = 0;
            for (c.operands) |o| n = @max(n, switch (o) {
                .arm => |a| armCount(a, kind),
                .rest => |k| if (kind == .seqs) k + 1 else 0,
            });
            break :blk n;
        },
        .same_arms => |sa| @max(patCount(sa.scrutinee.*, kind), if (kind == .regions) sa.region + 1 else 0),
        .tag_arm => |k| if (kind == .regions) k + 1 else 0,
        .rest => |k| if (kind == .seqs) k + 1 else 0,
        .identity => 0,
        .absorbing => |k| if (kind == .vars) k + 1 else 0,
        .lit_switch => |ls| @max(
            @max(patCount(ls.scrutinee.*, kind), patCount(ls.key.*, kind)),
            @max(armCount(ls.arms[0], kind), armCount(ls.arms[1], kind)),
            if (kind == .owners) ownerPatCount(ls.owner) else 0,
        ),
    };
}

fn armCount(a: Arm, kind: Kind) u8 {
    return switch (a) {
        .lit => 0,
        .region => |k| if (kind == .regions) k + 1 else 0,
        .value => |p| patCount(p.*, kind),
    };
}

fn ownerPatCount(o: OwnerPat) u8 {
    return switch (o) {
        .fixed => 0,
        .bind => |k| k + 1,
    };
}

/// A 64-bit fingerprint of the table, for `Code.version` (I11): any change to
/// a row changes it.
pub fn fingerprint() u64 {
    var h = std.hash.Wyhash.init(0);
    for (rules) |r| {
        h.update(r.step);
        h.update(&.{ @backingInt(r.tier), @backingInt(r.root) });
        h.update(&.{@intCast(r.args.len)});
        for (r.args) |p| hashPat(&h, p);
        if (r.root_prim) |rp| {
            h.update(&.{ 1, @backingInt(rp.method) });
            hashOwner(&h, rp.owner);
        } else h.update(&.{0});
        h.update(&.{@intCast(r.conds.len)});
        for (r.conds) |c| hashCond(&h, c);
        hashTmpl(&h, r.result);
    }
    return h.final();
}

fn hashOwner(h: *std.hash.Wyhash, o: OwnerPat) void {
    switch (o) {
        .fixed => |owner| h.update(&.{ 0, @backingInt(owner) }),
        .bind => |k| h.update(&.{ 1, k }),
    }
}

fn hashArm(h: *std.hash.Wyhash, a: Arm) void {
    switch (a) {
        .lit => |b| h.update(&.{ 0, @intFromBool(b) }),
        .region => |k| h.update(&.{ 1, k }),
        .value => |p| {
            h.update(&.{2});
            hashPat(h, p.*);
        },
    }
}

fn hashPat(h: *std.hash.Wyhash, p: Pat) void {
    switch (p) {
        .any => |k| h.update(&.{ 0, k }),
        .lit_bool => |b| h.update(&.{ 1, @intFromBool(b) }),
        .lit_int => |v| {
            h.update(&.{7});
            h.update(std.mem.asBytes(&v));
        },
        .prim => |pp| {
            h.update(&.{ 2, @backingInt(pp.method), @intCast(pp.args.len) });
            hashOwner(h, pp.owner);
            for (pp.args) |a| hashPat(h, a);
        },
        .op => |op| {
            h.update(&.{ 3, @backingInt(op.op), @intCast(op.args.len) });
            for (op.args) |a| hashPat(h, a);
        },
        .component => |c| h.update(&.{ 4, @backingInt(c.op), c.bind }),
        .bool_switch => |bs| {
            h.update(&.{5});
            hashPat(h, bs.scrutinee.*);
            for (bs.arms) |a| hashArm(h, a);
        },
        .connective => |c| {
            h.update(&.{ 6, @backingInt(c.op), @intCast(c.operands.len) });
            for (c.operands) |o| switch (o) {
                .arm => |a| {
                    h.update(&.{0});
                    hashArm(h, a);
                },
                .rest => |k| h.update(&.{ 1, k }),
            };
        },
        .same_arms => |sa| {
            h.update(&.{ 8, sa.region });
            hashPat(h, sa.scrutinee.*);
        },
        .tag_arm => |k| h.update(&.{ 9, k }),
        .rest => |k| h.update(&.{ 10, k }),
        .identity => h.update(&.{11}),
        .absorbing => |k| h.update(&.{ 12, k }),
        .lit_switch => |ls| {
            h.update(&.{13});
            hashPat(h, ls.scrutinee.*);
            hashOwner(h, ls.owner);
            hashPat(h, ls.key.*);
            for (ls.arms) |a| hashArm(h, a);
        },
    }
}

fn hashTmpl(h: *std.hash.Wyhash, t: Tmpl) void {
    switch (t) {
        .var_ => |k| h.update(&.{ 0, k }),
        .prim => |pp| {
            h.update(&.{ 1, @backingInt(pp.method), @intCast(pp.args.len) });
            hashOwner(h, pp.owner);
            for (pp.args) |a| hashTmpl(h, a);
        },
        .bool_switch => |bs| {
            h.update(&.{2});
            hashTmpl(h, bs.scrutinee.*);
            for (bs.arms) |a| switch (a) {
                .region => |k| h.update(&.{ 0, k }),
                .value => |v| {
                    h.update(&.{1});
                    hashTmpl(h, v.*);
                },
            };
        },
        .and_ => |ops| {
            h.update(&.{3});
            hashOperands(h, ops);
        },
        .or_ => |ops| {
            h.update(&.{4});
            hashOperands(h, ops);
        },
        .lit_bool => |b| h.update(&.{ 5, @intFromBool(b) }),
        .region_value => |k| h.update(&.{ 6, k }),
        .lit_int => |l| {
            h.update(&.{7});
            h.update(std.mem.asBytes(&l.value));
            hashOwner(h, l.owner);
        },
        .negation => |v| {
            h.update(&.{8});
            hashTmpl(h, v.*);
        },
        .folded => h.update(&.{9}),
        .rest => |k| h.update(&.{ 10, k }),
        .lit_switch => |ls| {
            h.update(&.{11});
            hashTmpl(h, ls.scrutinee.*);
            hashTmpl(h, ls.key.*);
            for (ls.arms) |a| switch (a) {
                .region => |k| h.update(&.{ 0, k }),
                .value => |v| {
                    h.update(&.{1});
                    hashTmpl(h, v.*);
                },
            };
        },
    }
}

fn hashOperands(h: *std.hash.Wyhash, ops: []const OperandTmpl) void {
    h.update(&.{@intCast(ops.len)});
    for (ops) |o| switch (o) {
        .value => |t| {
            h.update(&.{0});
            hashTmpl(h, t.*);
        },
        .region => |k| h.update(&.{ 1, k }),
        .rest => |k| h.update(&.{ 2, k }),
        .negated_rest => |k| h.update(&.{ 3, k }),
    };
}

fn hashCond(h: *std.hash.Wyhash, c: Cond) void {
    switch (c) {
        .int_owner => |k| h.update(&.{ 0, k }),
        .not_float_owner => |k| h.update(&.{ 1, k }),
        .is_lit => |k| h.update(&.{ 2, k }),
        .speculatable => |k| h.update(&.{ 3, k }),
        .nonzero_lit => |k| h.update(&.{ 4, k }),
        .movable => |k| h.update(&.{ 5, k }),
        .movable_rest => |k| h.update(&.{ 6, k }),
        .polarity_flips => |k| h.update(&.{ 7, k }),
        .folds => h.update(&.{8}),
        .same_ty => |k| h.update(&.{ 9, k }),
        .speculatable_rest => |k| h.update(&.{ 10, k }),
        .lit_bool_switch => |k| h.update(&.{ 11, k }),
        .not_lit => |k| h.update(&.{ 12, k }),
    }
}

const Counts = struct { vars: u8, owners: u8, regions: u8, seqs: u8 };

test "every rule's variables and owners are bound before its result reads them" {
    for (rules) |r| {
        const counts: Counts = .{ .vars = varCount(r), .owners = ownerVarCount(r), .regions = regionVarCount(r), .seqs = seqVarCount(r) };
        var lits: [16]bool = @splat(false);
        for (r.conds) |c| if (c == .is_lit) {
            lits[c.is_lit] = true;
        };
        for (r.args) |p| markKeys(p, &lits);
        try checkTmpl(r.result, counts, r.conds, &lits, false);
        for (r.conds) |c| switch (c) {
            .int_owner, .not_float_owner => |k| try std.testing.expect(k < counts.owners),
            .is_lit, .speculatable, .nonzero_lit, .polarity_flips, .same_ty, .lit_bool_switch, .not_lit => |k| try std.testing.expect(k < counts.vars),
            .movable => |k| try std.testing.expect(k < counts.regions),
            .movable_rest, .speculatable_rest => |k| try std.testing.expect(k < counts.seqs),
            .folds => try std.testing.expect(r.root == .prim and r.tier == .evaluation),
        };
        // Only an evaluation row computes its result.
        try std.testing.expectEqual(r.tier == .evaluation, r.result == .folded);
        if (r.root_prim != null) try std.testing.expectEqual(Op.prim, r.root);
        if (r.root == .switch_) try std.testing.expect(r.args.len == 1 and (r.args[0] == .bool_switch or r.args[0] == .same_arms or r.args[0] == .tag_arm or r.args[0] == .lit_switch));
        for (r.args) |p| try std.testing.expect(!nestsRootOnly(p, true));
        // A run, an identity and an absorber stand only among an associative builtin's operands.
        for (r.args) |p| if (p == .rest or p == .identity or p == .absorbing) try std.testing.expect(r.root_prim != null and prims.associativeOf(r.root_prim.?.method));
        for (r.args) |p| if (p == .absorbing) try std.testing.expect(prims.absorbingInt(.i64, r.root_prim.?.method) != null);
        if (r.root == .and_ or r.root == .or_) try std.testing.expect(r.args.len == 1 and r.args[0] == .connective and r.args[0].connective.op == r.root);
        // A pattern binds each sequence variable once, and a result splices
        // each once, so no run of operands is matched or built twice.
        var bound: [8]u8 = @splat(0);
        for (r.args) |p| countSeqBinds(p, &bound);
        for (bound[0..counts.seqs]) |n| try std.testing.expectEqual(@as(u8, 1), n);
        // A bound arm is reused at most once, so no region gets two owners.
        var uses: [8]u8 = @splat(0);
        var splices: [8]u8 = @splat(0);
        countUses(r.result, &uses, &splices);
        for (uses, 0..) |u, k| {
            try std.testing.expect(u <= 1);
            if (u == 1) try std.testing.expect(k < counts.regions);
        }
        for (splices) |u| try std.testing.expect(u <= 1);
    }
}

// Whether a pattern the builder matches only at a `switch_` root appears
// below `p`'s top, or at its top when `top` is false.
fn nestsRootOnly(p: Pat, top: bool) bool {
    return switch (p) {
        .any, .lit_bool, .lit_int, .component, .rest => false,
        .identity, .absorbing => !top,
        .same_arms => |sa| !top or nestsRootOnly(sa.scrutinee.*, false),
        .tag_arm => !top,
        .lit_switch => |ls| nestsRootOnly(ls.scrutinee.*, false) or nestsRootOnly(ls.key.*, false) or armNestsRootOnly(ls.arms[0]) or armNestsRootOnly(ls.arms[1]),
        .prim => |pp| for (pp.args) |a| {
            if (a == .rest and !prims.associativeOf(pp.method)) break true;
            if (a != .rest and nestsRootOnly(a, false)) break true;
        } else false,
        .op => |op| for (op.args) |a| {
            if (nestsRootOnly(a, false)) break true;
        } else false,
        .bool_switch => |bs| nestsRootOnly(bs.scrutinee.*, false) or armNestsRootOnly(bs.arms[0]) or armNestsRootOnly(bs.arms[1]),
        .connective => |c| for (c.operands) |o| switch (o) {
            .arm => |a| if (armNestsRootOnly(a)) break true,
            .rest => {},
        } else false,
    };
}

fn armNestsRootOnly(a: Arm) bool {
    return switch (a) {
        .lit, .region => false,
        .value => |p| nestsRootOnly(p.*, false),
    };
}

// Marks the variables `p` binds as the key of a literal switch.
fn markKeys(p: Pat, lits: *[16]bool) void {
    switch (p) {
        .any, .lit_bool, .lit_int, .component, .tag_arm, .identity, .absorbing, .rest => {},
        .same_arms => |sa| markKeys(sa.scrutinee.*, lits),
        .prim => |pp| for (pp.args) |a| markKeys(a, lits),
        .op => |op| for (op.args) |a| markKeys(a, lits),
        .bool_switch => |bs| {
            markKeys(bs.scrutinee.*, lits);
            for (bs.arms) |a| if (a == .value) markKeys(a.value.*, lits);
        },
        .lit_switch => |ls| {
            if (ls.key.* == .any) lits[ls.key.any] = true;
            markKeys(ls.scrutinee.*, lits);
            for (ls.arms) |a| if (a == .value) markKeys(a.value.*, lits);
        },
        .connective => |c| for (c.operands) |o| switch (o) {
            .arm => |a| if (a == .value) markKeys(a.value.*, lits),
            .rest => {},
        },
    }
}

fn countSeqBinds(p: Pat, bound: *[8]u8) void {
    switch (p) {
        .any, .lit_bool, .lit_int, .component, .tag_arm, .identity, .absorbing => {},
        .rest => |k| bound[k] += 1,
        .same_arms => |sa| countSeqBinds(sa.scrutinee.*, bound),
        .prim => |pp| for (pp.args) |a| countSeqBinds(a, bound),
        .op => |op| for (op.args) |a| countSeqBinds(a, bound),
        .bool_switch => |bs| {
            countSeqBinds(bs.scrutinee.*, bound);
            for (bs.arms) |a| countArmSeqBinds(a, bound);
        },
        .lit_switch => |ls| {
            countSeqBinds(ls.scrutinee.*, bound);
            countSeqBinds(ls.key.*, bound);
            for (ls.arms) |a| countArmSeqBinds(a, bound);
        },
        .connective => |c| for (c.operands) |o| switch (o) {
            .arm => |a| countArmSeqBinds(a, bound),
            .rest => |k| bound[k] += 1,
        },
    }
}

fn countArmSeqBinds(a: Arm, bound: *[8]u8) void {
    switch (a) {
        .lit, .region => {},
        .value => |p| countSeqBinds(p.*, bound),
    }
}

fn countUses(t: Tmpl, uses: *[8]u8, splices: *[8]u8) void {
    switch (t) {
        .var_, .lit_bool, .lit_int, .folded => {},
        .rest => |k| splices[k] += 1,
        .prim => |p| for (p.args) |a| countUses(a, uses, splices),
        .bool_switch => |bs| {
            for (bs.arms) |a| switch (a) {
                .region => |k| uses[k] += 1,
                .value => |v| countUses(v.*, uses, splices),
            };
            countUses(bs.scrutinee.*, uses, splices);
        },
        .and_, .or_ => |ops| for (ops) |o| switch (o) {
            .value => |v| countUses(v.*, uses, splices),
            .region => |k| uses[k] += 1,
            .rest, .negated_rest => |k| splices[k] += 1,
        },
        .region_value => |k| uses[k] += 1,
        .negation => |v| countUses(v.*, uses, splices),
        .lit_switch => |ls| {
            countUses(ls.scrutinee.*, uses, splices);
            countUses(ls.key.*, uses, splices);
            for (ls.arms) |a| switch (a) {
                .region => |k| uses[k] += 1,
                .value => |v| countUses(v.*, uses, splices),
            };
        },
    }
}

// `in_chain`: `t` is an argument of an associative builtin's template, where a run may stand.
// `lits`: the pattern variables that are literals, by a condition or as a key.
fn checkTmpl(t: Tmpl, counts: Counts, conds: []const Cond, lits: *const [16]bool, in_chain: bool) error{TestUnexpectedResult}!void {
    switch (t) {
        .var_ => |k| try std.testing.expect(k < counts.vars),
        .prim => |p| {
            switch (p.owner) {
                .fixed => {},
                .bind => |k| try std.testing.expect(k < counts.owners),
            }
            for (p.args) |a| try checkTmpl(a, counts, conds, lits, prims.associativeOf(p.method));
        },
        .rest => |k| try std.testing.expect(in_chain and k < counts.seqs),
        .bool_switch => |bs| {
            try checkTmpl(bs.scrutinee.*, counts, conds, lits, false);
            for (bs.arms) |a| switch (a) {
                .region => |k| try std.testing.expect(k < counts.regions),
                .value => |v| try checkTmpl(v.*, counts, conds, lits, false),
            };
        },
        // An empty `And` or `Or` has no first operand to build.
        .and_, .or_ => |ops| {
            try std.testing.expect(ops.len > 0);
            for (ops) |o| switch (o) {
                .value => |v| try checkTmpl(v.*, counts, conds, lits, false),
                .region => |k| try std.testing.expect(k < counts.regions),
                .rest, .negated_rest => |k| try std.testing.expect(k < counts.seqs),
            };
        },
        // The builder builds the literal without a range check, so it must
        // fit every integer type the owner can be.
        .lit_int => |l| switch (l.owner) {
            .fixed => |o| {
                const ty = o.int() orelse return error.TestUnexpectedResult;
                try std.testing.expect(l.value >= ty.min() and l.value <= ty.max());
            },
            .bind => |k| {
                try std.testing.expect(k < counts.owners);
                for (conds) |c| {
                    if (c == .int_owner and c.int_owner == k) break;
                } else return error.TestUnexpectedResult;
                try std.testing.expect(l.value >= 0 and l.value <= std.math.maxInt(i8));
            },
        },
        .region_value => |k| try std.testing.expect(k < counts.regions),
        .negation => |v| try checkTmpl(v.*, counts, conds, lits, false),
        // The key is a variable that a condition or a pattern's key makes a literal.
        .lit_switch => |ls| {
            try checkTmpl(ls.scrutinee.*, counts, conds, lits, false);
            try std.testing.expect(ls.key.* == .var_ and lits[ls.key.var_]);
            for (ls.arms) |a| switch (a) {
                .region => |k| try std.testing.expect(k < counts.regions),
                .value => |v| try checkTmpl(v.*, counts, conds, lits, false),
            };
        },
        .lit_bool => {},
        .folded => for (conds) |c| {
            if (c == .folds) break;
        } else return error.TestUnexpectedResult,
    }
}
