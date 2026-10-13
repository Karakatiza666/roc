//! Fuzzing for reification: the R fuzzer (L4) and the soundness differential
//! (L5) of `roc-reify-normalization-plan.md` 5.1.
//!
//! Each input is a case of `reify.fuzz_gen`: one generated function printed
//! twice under refactors in R. `compile.reify_fuzz.runCase` checks that the
//! two prints describe as one normal form, and that the normal form computes
//! the value Roc computes. A disagreement panics, so AFL records the input.
//!
//! To build just the repro executable:
//!   zig build build-repro-reify
//!
//! To run one input:
//!   ./zig-out/bin/repro-reify --verbose <seed_file>
//!
//! To run with AFL++:
//!   zig build -Dfuzz
//!   mkdir -p /tmp/roc-reify-corpus
//!   printf '\0' > /tmp/roc-reify-corpus/seed
//!   ./zig-out/AFLplusplus/bin/afl-fuzz -i /tmp/roc-reify-corpus -o /tmp/roc-reify-out zig-out/bin/fuzz-reify

const std = @import("std");
const build_options = @import("build_options");
const compile = @import("compile");
const eval = @import("eval");
const CoreCtx = @import("ctx").CoreCtx;

const tmp_root = "/tmp/roc-fuzz-reify";

pub export fn zig_fuzz_init() void {}

pub export fn zig_fuzz_test(buf: [*]u8, len: isize) void {
    zig_fuzz_test_inner(buf, len, false);
}

pub fn zig_fuzz_test_inner(buf: [*]u8, len: isize, debug: bool) void {
    var gpa_impl = std.heap.DebugAllocator(.{ .stack_trace_frames = build_options.debug_gpa_stack_trace_frames }){};
    defer {
        _ = build_options.debugGpaOk(gpa_impl.deinit());
    }
    const gpa = gpa_impl.allocator();
    const input = buf[0..@intCast(len)];
    const io = std.Io.Threaded.global_single_threaded.io();

    var builtins = eval.BuiltinModules.init(std.heap.page_allocator) catch @panic("failed to load the builtin modules");
    defer builtins.deinit();

    std.Io.Dir.createDirAbsolute(io, tmp_root, .default_dir) catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => @panic("failed to create the reify fuzz directory"),
    };
    var dir = std.Io.Dir.openDirAbsolute(io, tmp_root, .{}) catch @panic("failed to open the reify fuzz directory");
    defer dir.close(io);

    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const ctx = CoreCtx.default(gpa, arena.allocator(), io);
    const verdict = compile.reify_fuzz.runCase(ctx, &builtins, dir, input) catch |err| std.debug.panic("reify fuzz case failed: {t}", .{err});
    if (debug) std.debug.print("verdict: {t}\n", .{verdict});
}
