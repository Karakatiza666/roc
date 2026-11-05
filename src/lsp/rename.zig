//! Name and scope rules for `textDocument/rename`.
//!
//! A rename may only change what a binding is called. In Roc part of what a
//! name *means* is spelled in the name itself: a trailing `!` marks a value
//! effectful and a leading `_` marks it deliberately unused, while upper and
//! lower case separate types and tags
//! from values. Rewriting `foo` to `foo!` is therefore not a rename—it is an
//! edit the type checker would reject, or worse, silently accept with
//! different meaning.
//!
//! The rules are read off the real tokenizer and `Ident.Attributes` rather
//! than restated here, so a change to what Roc considers an identifier cannot
//! drift away from what rename accepts.

const std = @import("std");
const Allocator = std.mem.Allocator;
const base = @import("base");
const can = @import("can");
const parse = @import("parse");

const cir_queries = @import("cir_queries.zig");
const module_lookup = @import("module_lookup.zig");
const scope_map = @import("scope_map.zig");

const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const Ident = base.Ident;
const Token = parse.tokenize.Token;

/// Why a requested new name cannot be used.
pub const Rejection = enum {
    /// The text is not exactly one Roc identifier.
    not_an_identifier,
    /// The text is an identifier, but not the same kind of identifier as the
    /// name being replaced.
    changes_ident_kind,

    /// A message suitable for reporting back to the editor.
    pub fn message(self: Rejection) []const u8 {
        return switch (self) {
            .not_an_identifier => "the new name must be a single Roc identifier",
            .changes_ident_kind => "the new name must be the same kind of identifier as the old one: " ++
                "upper- and lowercase names are not interchangeable, and the `!` and `_` markers carry meaning",
        };
    }
};

/// What a name spells, as the compiler reads it.
const NameShape = struct {
    tag: Token.Tag,
    attributes: Ident.Attributes,

    fn eql(self: NameShape, other: NameShape) bool {
        return self.tag == other.tag and
            self.attributes.effectful == other.attributes.effectful and
            self.attributes.ignored == other.attributes.ignored;
    }
};

/// Check whether `new_name` may replace `old_name`.
///
/// Returns null when the rename is allowed. Both names are run through the
/// tokenizer, so "is this an identifier" is answered by the compiler rather
/// than by a rule restated here.
pub fn checkNewName(
    allocator: Allocator,
    old_name: []const u8,
    new_name: []const u8,
) Allocator.Error!?Rejection {
    const new_shape = try nameShape(allocator, new_name) orelse return .not_an_identifier;

    // The old name came out of the CIR, so it tokenizes by construction; if it
    // somehow does not, refuse rather than guess what kind of name it was.
    const old_shape = try nameShape(allocator, old_name) orelse return .changes_ident_kind;

    if (!new_shape.eql(old_shape)) return .changes_ident_kind;
    return null;
}

/// Tokenize `text` on its own and report what single identifier it spells.
///
/// Returns null when the text is anything else: empty, several tokens, a
/// keyword, punctuation, or an identifier the tokenizer complained about.
fn nameShape(allocator: Allocator, text: []const u8) Allocator.Error!?NameShape {
    if (text.len == 0) return null;

    var module_env = try can.ModuleEnv.init(allocator, text);
    defer module_env.deinit();

    var messages: [4]parse.tokenize.Diagnostic = undefined;
    var tokenizer = try parse.tokenize.Tokenizer.init(&module_env.common, allocator, text, &messages);
    try tokenizer.tokenize(allocator);
    var output = tokenizer.finishAndDeinit();
    defer output.tokens.deinit(allocator);

    if (output.messages.len != 0 or output.extra_messages_dropped != 0) return null;

    const tags = output.tokens.tokens.items(.tag);
    const regions = output.tokens.tokens.items(.region);

    // One identifier and the end of input, and the identifier must span the
    // whole text—otherwise the editor sent something like `foo bar` or `foo=`.
    if (tags.len != 2 or tags[1] != .EndOfFile) return null;
    if (!isIdentifierTag(tags[0])) return null;
    if (regions[0].start.offset != 0 or regions[0].end.offset != text.len) return null;

    return NameShape{
        .tag = tags[0],
        .attributes = Ident.Attributes.fromString(text),
    };
}

/// Whether a token tag names something a binding can be called.
fn isIdentifierTag(tag: Token.Tag) bool {
    return tag == .LowerIdent or tag == .UpperIdent or tag == .NamedUnderscore;
}

/// The binding a rename request refers to.
pub const Target = struct {
    pattern: CIR.Pattern.Idx,
    ident: Ident.Idx,
};

/// Resolve a source offset to a binding that can be renamed.
///
/// Only a plain `assign` pattern names a single binding whose every occurrence
/// this server can account for. Destructuring, literal, and tag patterns bind
/// through structure that a name-for-name rewrite cannot express, so they are
/// refused rather than half-renamed.
pub fn targetAt(module_env: *ModuleEnv, offset: u32) ?Target {
    const pattern_idx = cir_queries.resolveSymbolAtOffset(module_env, offset) orelse return null;
    return switch (module_env.store.getSourcePattern(pattern_idx)) {
        .assign => |assign| .{ .pattern = pattern_idx, .ident = assign.ident },
        .var_assign => |assign| .{ .pattern = pattern_idx, .ident = assign.ident },
        .as,
        .applied_tag,
        .nominal,
        .nominal_external,
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
        .deferred_import_ref => base.invariant("compiler invariant violated: deferred import reference pattern reached a stage that runs after import resolution", .{}),
    };
}

/// Find the collected range that contains the given position.
pub fn rangeContaining(regions: []const cir_queries.LspRange, line: u32, character: u32) ?cir_queries.LspRange {
    for (regions) |range| {
        if (range.start_line != line or range.end_line != line) continue;
        if (character >= range.start_col and character <= range.end_col) return range;
    }
    return null;
}

/// What checking a new name against the surrounding scopes established.
pub const ScopeCheck = enum {
    /// No other binding of that name is live where the renamed one is.
    clear,
    /// Another such binding is live, so the rewrite would capture or shadow.
    taken,
    /// The renamed binding's extent was not found, so nothing was checked.
    scope_unavailable,
};

/// Whether renaming `target` to `new_name` would collide with another binding
/// of that name.
///
/// Rename rewrites text, but a name means whichever binding is live where
/// it is written. If a different `new_name` binding is live anywhere the
/// renamed one is, the rewrite silently repoints a reference: renaming `k`
/// in `|v| { helper = |k| k + v }` to `v` yields `|v| v + v`, which
/// compiles and computes something else.
///
/// Two bindings whose live ranges overlap cannot both be called
/// `new_name`, so an overlap is refused. Bindings in unrelated scopes do
/// not overlap and stay renameable.
pub fn checkNewNameAgainstScope(
    bindings: []const scope_map.Binding,
    module_env: *const ModuleEnv,
    target: Target,
    new_name: []const u8,
) ScopeCheck {
    var target_binding: ?scope_map.Binding = null;
    for (bindings) |binding| {
        if (binding.pattern_idx == target.pattern) {
            target_binding = binding;
            break;
        }
    }

    // Without the renamed binding's own extent there is nothing to compare
    // against. Refuse, but say which of the two happened:
    // "the name is taken" would be a claim about the code that has not
    // been established.
    const extent = target_binding orelse return .scope_unavailable;
    const target_item = module_lookup.associatedItemKey(module_env, target.ident);

    for (bindings) |binding| {
        if (binding.pattern_idx == target.pattern) continue;
        if (!bindingIsCalled(module_env, binding.ident, target_item, new_name)) continue;
        if (binding.visible_from <= extent.visible_to and extent.visible_from <= binding.visible_to) {
            return .taken;
        }
    }
    return .clear;
}

/// Whether a binding bound as `ident` would be called `new_name` after the
/// rename. The renamed associated item would be called `new_name` in its own
/// type, so a sibling item of that name collides with it, and so does a plain
/// binding that a bare use inside the type can be captured by.
fn bindingIsCalled(module_env: *const ModuleEnv, ident: Ident.Idx, target_item: ?ModuleEnv.MethodKey, new_name: []const u8) bool {
    if (std.mem.eql(u8, module_env.getIdentText(ident), new_name)) return true;
    const owner = target_item orelse return false;
    const item = module_lookup.associatedItemKey(module_env, ident) orelse return false;
    return item.owner == owner.owner and std.mem.eql(u8, module_env.getIdentText(item.methodIdent()), new_name);
}
