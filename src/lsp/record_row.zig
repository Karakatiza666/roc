//! The fields of a record type, gathered across its whole extension chain.

const std = @import("std");
const base = @import("base");
const types = @import("types");

const Allocator = std.mem.Allocator;

/// The fields of `record` and of every row its extension chain reaches,
/// following aliases. Unification can leave a record's fields spread over
/// several rows of one chain. A label that occurs more than once names one
/// field, and its innermost occurrence stands for it (design.md "Row Union
/// Normalization"). The fields come sorted by name, as rows are sorted
/// elsewhere in the compiler, so the order does not depend on the order the
/// names were first interned. The caller frees the slice with `allocator`.
pub fn gather(allocator: Allocator, type_store: *const types.Store, idents: *const base.Ident.Store, record: types.Record) Allocator.Error![]types.RecordField {
    var fields = std.ArrayList(types.RecordField).empty;
    errdefer fields.deinit(allocator);
    // A chain that returns to a row it already reached has no more fields.
    var seen = std.AutoHashMapUnmanaged(types.Var, void).empty;
    defer seen.deinit(allocator);

    var row_fields = record.fields;
    var ext = record.ext;
    while (true) {
        const slice = type_store.getRecordFieldsSlice(row_fields);
        const outer_end = fields.items.len;
        for (slice.items(.name), slice.items(.presence)) |name, presence| {
            for (fields.items[0..outer_end]) |*outer| {
                if (outer.name.eql(name)) {
                    outer.* = .{ .name = name, .presence = presence };
                    break;
                }
            } else try fields.append(allocator, .{ .name = name, .presence = presence });
        }

        const next = while (true) {
            const resolved = type_store.resolveVar(ext);
            if ((try seen.getOrPut(allocator, resolved.var_)).found_existing) break null;
            switch (resolved.desc.content) {
                .alias => |alias| ext = type_store.getAliasBackingVar(alias),
                .structure => |flat_type| switch (flat_type) {
                    .record => |ext_record| break ext_record,
                    .tuple, .nominal_type, .fn_pure, .fn_effectful, .fn_unbound, .empty_record, .tag_union, .empty_tag_union => break null,
                },
                .flex, .rigid, .field_presence, .err => break null,
            }
        };
        const ext_record = next orelse break;
        row_fields = ext_record.fields;
        ext = ext_record.ext;
    }

    std.mem.sort(types.RecordField, fields.items, idents, nameLessThan);
    return fields.toOwnedSlice(allocator);
}

fn nameLessThan(idents: *const base.Ident.Store, a: types.RecordField, b: types.RecordField) bool {
    return std.mem.lessThan(u8, idents.getText(a.name), idents.getText(b.name));
}
