//! The ledger of the rule-derivation tool (`roc-reify-rule-derivation.md`
//! 3.6): what triage decided about each group the tool reported.
//!
//! | List | Holds | Checked by |
//! |---|---|---|
//! | `admitted` | the rows `--admit` wrote into the table, with the iteration | the rows' generated tests |
//! | `rejected` | equations kept out of the table, with the criterion | their witnesses still normalize apart (L3) |
//! | `open` | pairs filed against the algorithm that must join them | their witnesses still normalize apart; a pair that meets names its entry to remove |
//!
//! Terms are in the tool's term syntax (`derive/term.zig`). `ledger.zon`
//! is written by the tool's triage commands and read here at compile time.

/// A row `--admit` wrote.
pub const Admitted = struct {
    /// The row's `step`.
    step: []const u8,
    iteration: u32,
    /// The group's equation.
    equation: []const u8,
};

/// A rejected equation or a filed pair.
pub const Entry = struct {
    /// Where the witnesses come from: a signature such as `S1`, whose base
    /// variables they read, or `step1` for a critical pair's normal forms.
    source: []const u8,
    /// The equation, each side a term whose variables stand for any term.
    lhs: []const u8,
    rhs: []const u8,
    /// For `rejected`, the criterion of 3.6; for `open`, the algorithm filed against.
    reason: []const u8,
    /// Two terms that the table normalizes apart and the equation relates.
    witness_left: []const u8,
    witness_right: []const u8,
};

/// The whole ledger.
pub const Ledger = struct {
    admitted: []const Admitted = &.{},
    rejected: []const Entry = &.{},
    open: []const Entry = &.{},
};

/// The ledger as `ledger.zon` holds it.
pub const current: Ledger = @import("ledger.zon");
