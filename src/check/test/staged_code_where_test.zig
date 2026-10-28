//! A `where` on a type variable that a staged `Code(row -> v)` argument fixes.
//!
//! The staged frame relates the call's own `Code(f)` parameter. It must not
//! take a copy of that parameter type, because a copy holds a second instance
//! of the `where` receiver `v`, which nothing fixes (surreal bug 04).
const TestEnv = @import("TestEnv.zig");

const lib_source =
    \\Lib :: {}.{
    \\    put : List(row), Code(row -> v), v -> U64 where [v.to_str : v -> Str]
    \\    put = |_rows, _path, value| value.to_str().count_utf8_bytes()
    \\
    \\    put_after : List(row), v, Code(row -> v) -> U64 where [v.to_str : v -> Str]
    \\    put_after = |_rows, value, _path| value.to_str().count_utf8_bytes()
    \\
    \\    put_fn : List(row), (row -> v), v -> U64 where [v.to_str : v -> Str]
    \\    put_fn = |_rows, _path, value| value.to_str().count_utf8_bytes()
    \\}
;

const app_prefix =
    \\import Lib
    \\
    \\R : { a : I64 }
    \\
    \\rows : List(R)
    \\rows = []
    \\
    \\five : I64
    \\five = 5
    \\
    \\poly = || { crash "x" }
    \\
;

fn checkAgainstLib(comptime app_suffix: []const u8, comptime body: fn (*TestEnv) TestEnv.TestEnvError!void) !void {
    var lib_env = try TestEnv.init("Lib", lib_source);
    defer lib_env.deinit();
    try lib_env.assertNoErrors();

    var app_env = try TestEnv.initWithImport("App", app_prefix ++ app_suffix, "Lib", &lib_env);
    defer app_env.deinit();
    try body(&app_env);
}

fn expectNoErrors(env: *TestEnv) TestEnv.TestEnvError!void {
    try env.assertNoErrors();
}

fn expectOneMismatch(env: *TestEnv) TestEnv.TestEnvError!void {
    try env.assertOneTypeError("Type Mismatch");
}

fn expectMissingMethod(env: *TestEnv) TestEnv.TestEnvError!void {
    try env.assertHasTypeError("Missing Method");
}

test "staged code where: a Code argument and a value fix the where receiver, as a plain function does" {
    try checkAgainstLib(
        \\with_code : U64
        \\with_code = Lib.put(rows, |r| r.a, five)
        \\
        \\with_fn : U64
        \\with_fn = Lib.put_fn(rows, |r| r.a, five)
    , expectNoErrors);
}

test "staged code where: a Code argument after the value fixes the where receiver" {
    try checkAgainstLib(
        \\out : U64
        \\out = Lib.put_after(rows, five, |r| r.a)
    , expectNoErrors);
}

test "staged code where: a mismatched value is one type error, with no unresolved receiver" {
    try checkAgainstLib(
        \\out : U64
        \\out = Lib.put(rows, |r| r.a, "s")
    , expectOneMismatch);
}

test "staged code where: a receiver nothing fixes is still an unresolved dispatch" {
    try checkAgainstLib(
        \\out = Lib.put(rows, |_r| poly(), poly())
    , expectMissingMethod);
}
