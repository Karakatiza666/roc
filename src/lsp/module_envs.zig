//! The checked module env that a reference in one module names.
//!
//! An import names its module through the importer's own import data. A type
//! or a resolved associated item names its module by content identity, as the
//! checker does. Nothing here searches modules by name.

const std = @import("std");
const base = @import("base");
const can = @import("can");
const compile = @import("compile");

const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const BuildEnv = compile.BuildEnv;
const ModuleState = compile.coordinator.ModuleState;

/// The Builtin module env. Every build env of the server shares it.
pub fn builtin(build_env: *BuildEnv) *ModuleEnv {
    return build_env.builtin_modules.builtin_module.env;
}

/// The env of the module that `from_env` names by `identity`.
pub fn forIdentity(build_env: *BuildEnv, from_env: *ModuleEnv, identity: base.ModuleIdentity.Idx) ?*ModuleEnv {
    if (identity == from_env.selfModuleIdentity()) return from_env;
    const target_hash = from_env.moduleIdentityHash(identity);
    const builtin_env = builtin(build_env);
    if (builtin_env.contentIdentityHash()) |builtin_hash| {
        if (std.mem.eql(u8, builtin_hash, target_hash)) return builtin_env;
    }
    const module_state = stateForContentIdentity(build_env, target_hash) orelse return null;
    return module_state.moduleEnv();
}

/// The env of the module that declares a type, given the type's origin in
/// `from_env`'s identity table.
pub fn forTypeOrigin(build_env: *BuildEnv, from_env: *ModuleEnv, origin_module: base.ModuleIdentity.Idx, builtin_origin: bool) ?*ModuleEnv {
    if (builtin_origin) return builtin(build_env);
    return forIdentity(build_env, from_env, origin_module);
}

/// The env that import `import_idx` of `from_env`, the module at
/// `module_path`, was checked against.
pub fn forImport(build_env: *BuildEnv, from_env: *ModuleEnv, module_path: []const u8, import_idx: CIR.Import.Idx) ?*ModuleEnv {
    const import_name = from_env.common.getString(from_env.imports.imports.items.items[@backingInt(import_idx)]);
    return build_env.importedModuleEnv(module_path, import_name);
}

/// The env of the import that binds `qualifier` as a module qualifier in
/// `from_env`, the module at `module_path`.
pub fn forQualifier(build_env: *BuildEnv, from_env: *ModuleEnv, module_path: []const u8, qualifier: []const u8) ?*ModuleEnv {
    const import_name = importNameForQualifier(from_env, qualifier) orelse return null;
    return build_env.importedModuleEnv(module_path, import_name);
}

/// The name of the import that binds `qualifier` as a module qualifier in
/// `from_env`, or null when no import binds it.
fn importNameForQualifier(from_env: *ModuleEnv, qualifier: []const u8) ?[]const u8 {
    for (from_env.store.sliceStatements(from_env.all_statements)) |stmt_idx| {
        const stmt = from_env.store.getSourceStatement(stmt_idx);
        if (stmt != .s_import) continue;
        const alias_tok = stmt.s_import.alias_tok orelse continue;
        if (std.mem.eql(u8, from_env.common.idents.getText(alias_tok), qualifier)) {
            return from_env.common.idents.getText(stmt.s_import.module_name_tok);
        }
    }
    return null;
}

/// The module state of the build whose env has content identity `hash`.
pub fn stateForContentIdentity(build_env: *BuildEnv, hash: *const base.ModuleIdentity.Hash) ?*ModuleState {
    const coord = build_env.coordinator orelse return null;
    var pkg_it = coord.packages.iterator();
    while (pkg_it.next()) |entry| {
        for (entry.value_ptr.*.modules.items) |*module_state| {
            const module_env = module_state.moduleEnv() orelse continue;
            const module_hash = module_env.contentIdentityHash() orelse continue;
            if (std.mem.eql(u8, module_hash, hash)) return module_state;
        }
    }
    return null;
}
