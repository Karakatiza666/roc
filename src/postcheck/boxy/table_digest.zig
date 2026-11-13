//! The digest of one Code instance table of a module's code output: what a
//! `.boxy` unit of another module reads of the table when it fills a type
//! table from it (`Tables.Recipe.instance_entry`, design.md "Code Instance
//! Tables"). The unit's object cache entry records the digest of each such
//! table it read, and a restore checks it against the table now.

const std = @import("std");
const base = @import("base");
const check = @import("check");

const checked = check.CheckedModule;
const code_output = check.CodeOutput;

/// The digest of table `table` of `view`'s code output. `names` gives the
/// link name of a module by its checked module key (`nameOf`), as the unit's
/// lowering names modules, so the digest is the same in the build and in a
/// later restore of the same link.
pub fn instanceTableDigest(view: checked.ImportedModuleView, table: u32, names: anytype) [32]u8 {
    var hasher = base.Sha256.init(.{});
    hasher.update("roc.boxy.instance_table.v1");
    const output = view.code_output;
    std.debug.assert(table < output.tables.len); // a recorded read names a table of the module
    const record = output.tables[table];
    // A refused table serves no template and has no entry.
    if (record.template.template == code_output.no_template) {
        hasher.update("refused");
        return hasher.finalResult();
    }
    hasher.update(&names.nameOf(record.template.module.bytes));
    hasher.update(std.mem.asBytes(&record.template.template));
    hasher.update(std.mem.asBytes(&record.entries.len));
    // A node entry's description is the table's module's object's thunk,
    // named by the table and the entry, so the reader depends on its kind
    // and not on its content.
    const id: code_output.TableId = @fromBackingInt(table);
    for (0..record.entries.len) |position| {
        const entry = output.entry(id, @intCast(position));
        hasher.update(@tagName(std.meta.activeTag(entry)));
        switch (entry) {
            .forward => |forward| hasher.update(std.mem.asBytes(&@as(u32, @backingInt(forward)))),
            .node, .refused => {},
        }
    }
    return hasher.finalResult();
}
