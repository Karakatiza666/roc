//! Staging: a Roc function named where a `Code` is expected becomes a
//! description, and a stage written in Roc reads it while the compiler runs.
//!
//! Every case here goes the whole way through `roc build`: the checker records
//! the site, publication walks the named function into the module's const
//! store, lowering restores the stored description at the site, and the stage
//! turns it into the value `main` inspects.

const TestCase = @import("parallel_runner.zig").TestCase;

/// A stage that names every `Code.Ir` node it meets. Shared by the cases below
/// so each one differs only in the function it stages.
const stage =
    \\Stage :: {}.{
    \\    describe : Code(F32 -> F32) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir|
    \\        match ir {
    \\            Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\            Param(name, _m) => "param ${name}"
    \\            Local(name, _m) => "local ${name}"
    \\            Let(name, value, body, _m) => "let ${name} = ${Stage.node(value)} in ${Stage.node(body)}"
    \\            Lit(_l, _m) => "lit"
    \\            Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\            Unary(op, value, _m) => "${op} ${Stage.node(value)}"
    \\            Call(name, _a, _m) => "call ${name}"
    \\            Field(record, name, _m) => "${Stage.node(record)}.${name}"
    \\            Index(_r, _i, _m) => "index"
    \\            MakeRecord(_f, _m) => "record"
    \\            MakeTuple(_e, _m) => "tuple"
    \\            MakeList(_e, _m) => "list"
    \\            If(_c, _t, _e, _m) => "if"
    \\            MakeTag(name, _p, _m) => "tag ${name}"
    \\            Match(_s, _b, _m) => "match"
    \\            Crash(_message, _m) => "crash"
    \\            Derived(name, _s, _a, _m) => "derived ${name}"
    \\        }
    \\}
    \\
;

const staged_binop = stage ++
    \\double : F32 -> F32
    \\double = |x| x * 2.0.F32
    \\main = Stage.describe(double)
;

// A `let` in the staged body stays a `Let` node. That is the property a shader
// stage needs: one Roc binding becomes one GLSL local, used twice.
const staged_let = stage ++
    \\wobble : F32 -> F32
    \\wobble = |x| {
    \\    wave = x * 2.0.F32
    \\    wave + wave
    \\}
    \\main = Stage.describe(wobble)
;

// A lambda written inside the staged function is a `Lambda` where it stands,
// and a name it reads from the lambda around it is a parameter the description
// already binds, so it describes as a `Param` rather than as a capture.
const staged_nested_lambda =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(params, body, _m) => "(${Str.join_with(params.map(|p| p.name), ", ")}) -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\adder : F32 -> (F32 -> F32)
    \\adder = |a| |b| a + b
    \\main = Stage.describe(adder)
;

// `!b`, `Bool.not(b)` and `b.not()` are one operation, so all three describe
// as the one `Unary` node a translator already handles.
const staged_not_spellings =
    \\Stage :: {}.{
    \\    describe : Code(F32 -> Bool) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(_params, Unary(op, _value, _u), _m) => op
    \\        _ => "not an inversion"
    \\    }
    \\}
    \\
    \\bang : F32 -> Bool
    \\bang = |x| !(x > 1.0.F32)
    \\
    \\qualified : F32 -> Bool
    \\qualified = |x| Bool.not(x > 1.0.F32)
    \\
    \\dispatched : F32 -> Bool
    \\dispatched = |x| (x > 1.0.F32).not()
    \\
    \\main = Str.join_with([Stage.describe(bang), Stage.describe(qualified), Stage.describe(dispatched)], " ")
;

/// A stage that prints each row's name beside the types its parameters take,
/// so two instantiations of one definition are told apart by what they were
/// fixed to rather than by their names alone.
const instantiation_stage =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(Stage.row), " ; ")
    \\
    \\    row : { ir : Code.Ir, name : Str } -> Str
    \\    row = |d| match d.ir {
    \\        Lambda(params, _body, _m) => "${d.name}(${Str.join_with(params.map(|p| Stage.ty(p.ty)), ", ")})"
    \\        _ => d.name
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        F32 => "F32"
    \\        Str => "Str"
    \\        Record(fs) => "{${Str.join_with(fs.map(|f| "${f.name}: ${Stage.ty(f.ty)}"), ", ")}}"
    \\        _ => "other"
    \\    }
    \\}
    \\
;

// A generic callee is one row per instantiation: the body is one, and what it
// reads at is not, so a translator emits one function per type it is used at.
const staged_generic_instantiations = instantiation_stage ++
    \\pick : a, b -> a
    \\pick = |p, _q| p
    \\
    \\mix : F32 -> F32
    \\mix = |x| pick(x, "s") + pick(x, 1.0.F32)
    \\main = Stage.describe(mix)
;

// A generic callee that calls a generic function writes the inner call in its
// own variables, so the inner row is keyed by what the outer call fixed them
// to rather than by a type that still holds a variable.
const staged_generic_nested = instantiation_stage ++
    \\id : a -> a
    \\id = |v| v
    \\
    \\wrap : b -> b
    \\wrap = |v| id(v)
    \\
    \\mix : F32 -> F32
    \\mix = |x| wrap(x)
    \\main = Stage.describe(mix)
;

// A variable the scheme reaches only through a record is fixed by the record
// the call passes, so the row reads its field at the type the call fixed.
//
// The two calls pass records of one checked type id, which is why the `Ty`
// cache has to refuse a subtree a substitution answered inside: caching it
// would hand the second instantiation the first one's field type.
const staged_generic_record = instantiation_stage ++
    \\field : { v : a } -> a
    \\field = |r| r.v
    \\
    \\mix : F32 -> Str
    \\mix = |x| field({ v: x }).to_str().concat(field({ v: "s" }))
    \\main = Stage.describe(mix)
;

// A `where`-constrained callee dispatches on its own quantified variable, so
// the substitution is what turns `to_str` into a call named by the type the
// call fixed it to.
const staged_generic_where =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}"), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\show : a -> Str where [a.to_str : a -> Str]
    \\show = |v| v.to_str()
    \\
    \\plain : F32 -> Str
    \\plain = |v| v.to_str()
    \\
    \\label : F32 -> Str
    \\label = |x| show(x)
    \\
    \\direct : F32 -> Str
    \\direct = |x| plain(x)
    \\main = "${Stage.describe(label)} | ${Stage.describe(direct)}"
;

// A type-level statement declares a name for the checker and leaves no value
// behind, so the description passes over it and the block around it describes.
// Naming a type before a dispatch is how a codec call is written.
const staged_type_statement = stage ++
    \\aliased : F32 -> F32
    \\aliased = |x| {
    \\    Width : F32
    \\    k : Width
    \\    k = x * 2.0.F32
    \\    k + 1.0.F32
    \\}
    \\main = Stage.describe(aliased)
;

// `Shape.method(args)` dispatches on a type rather than a value, which is the
// form a derived codec is reached through. The dispatcher is the callee's own
// quantified variable, so the name the call carries is the one the
// instantiation fixed it to, and the row behind that name is the method's own
// body: the constrained body forwards the obligation, and the call that
// instantiated it names the target.
const staged_type_dispatch =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        MakeTag(name, _p, _m) => "tag ${name}"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\Format := [Default].{}
    \\
    \\Token := { raw : Str }.{
    \\    tag_of : Format, Token -> Str
    \\    tag_of = |_f, t| t.raw
    \\}
    \\
    \\name : value, Format -> Str where [value.tag_of : Format, value -> Str]
    \\name = |v, fmt| {
    \\    Shape : value
    \\    Shape.tag_of(fmt, v)
    \\}
    \\
    \\emit : Token -> Str
    \\emit = |t| name(t, Format.Default)
    \\main = Stage.describe(emit)
;

// A method call names a row the way a plain call does, so a translator
// resolving `Token.label` has a definition to resolve it against rather than a
// name with nothing behind it.
const staged_method_definition =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Field(record, name, _m) => "${Stage.node(record)}.${name}"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\Token := { raw : Str }.{
    \\    label : Token -> Str
    \\    label = |t| t.raw
    \\}
    \\
    \\name : Token -> Str
    \\name = |t| t.label()
    \\main = Stage.describe(name)
;

// A parametric nominal's backing is the declaration's template, written in the
// nominal's own variables, and what a use fixes them to is on the use. Reading
// the two together is what makes `Box(F32)` a `Box` of `F32`, and it is what a
// derived `map` needed: the mapping function is a nested `Lambda`, and the
// subject is the nominal the compiler derived against.
const staged_parametric_nominal =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(params, body, _m) => "${Str.join_with(params.map(|p| Stage.ty(p.ty)), ", ")} => ${Stage.node(body)}"
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(params, body, _m) => "(${Str.join_with(params.map(|p| p.name), ", ")}) -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Lit(_l, _m) => "lit"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        Derived(name, subject, args, _m) => "derived ${name} of ${Stage.ty(subject)}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        F32 => "F32"
    \\        Named(name, backing) => "${name}(${Stage.ty(backing)})"
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(|v| "${v.name}(${Str.join_with(v.payloads.map(Stage.ty), ", ")})"), ", ")}]"
    \\        _ => "?"
    \\    }
    \\}
    \\
    \\Crate(a) := [Empty, Full(a)].{
    \\    map : _
    \\}
    \\
    \\bump : Crate(F32) -> Crate(F32)
    \\bump = |b| b.map(|v| v * 2.0.F32)
    \\main = Stage.describe(bump)
;

// A function argument has no node, so the call that passes one resolves it:
// the parameter binds to the definition the argument names, and the body
// describes a call on that parameter as a call on that definition. One row per
// set of callees, the way a generic definition takes one per instantiation. A
// lambda written at the call site is lifted into a row of its own and named
// after the parameter it binds, because the lambda binds no name.
const staged_function_argument =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(params, body, _m) => "(${Str.join_with(params.map(|p| p.name), ", ")}) -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Lit(_l, _m) => "lit"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\apply_to : (F32 -> F32), F32 -> F32
    \\apply_to = |f, x| f(x)
    \\
    \\double : F32 -> F32
    \\double = |y| y * 2.0.F32
    \\
    \\triple : F32 -> F32
    \\triple = |y| y * 3.0.F32
    \\
    \\named : F32 -> F32
    \\named = |x| apply_to(double, x) + apply_to(triple, x)
    \\
    \\written : F32 -> F32
    \\written = |x| apply_to(|y| y - 1.0.F32, x)
    \\main = "${Stage.describe(named)} | ${Stage.describe(written)}"
;

// A lambda a block bound is a row of its own, so the binding leaves no `Let`
// behind and the call names the row. The row is described with none of the
// scope around it, so what the lambda captured arrives as a leading parameter
// and the call site passes it first. Two functions can each write one called
// `step`, which is why a lifted row takes a serial.
const staged_local_lambda =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(params, body, _m) => "(${Str.join_with(params.map(|p| p.name), ", ")}) -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Lit(_l, _m) => "lit"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\plain : F32 -> F32
    \\plain = |x| {
    \\    step : F32 -> F32
    \\    step = |y| y * 2.0.F32
    \\    step(x)
    \\}
    \\
    \\capturing : F32 -> F32
    \\capturing = |x| {
    \\    step : F32 -> F32
    \\    step = |y| y * x
    \\    step(1.0.F32)
    \\}
    \\main = "${Stage.describe(plain)} | ${Stage.describe(capturing)}"
;

// A definition that hands back a function and the call that runs it are one
// row and one `Call`: the row gathers both lambdas' parameters, and the call
// passes the constructor's arguments before the applied ones. Bound first and
// run later is the same thing held in scope.
const staged_curried_call =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(params, body, _m) => "(${Str.join_with(params.map(|p| p.name), ", ")}) -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Lit(_l, _m) => "lit"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\scaler : F32 -> (F32 -> F32)
    \\scaler = |k| |x| x * k
    \\
    \\direct : F32 -> F32
    \\direct = |x| scaler(2.0.F32)(x)
    \\
    \\held : F32 -> F32
    \\held = |x| {
    \\    twice = scaler(2.0.F32)
    \\    twice(x)
    \\}
    \\main = "${Stage.describe(direct)} | ${Stage.describe(held)}"
;

// A format nominal the derived codec calls into, shared by the two codec cases
// below. The protocol fixes these method names, and a record of strings reaches
// only these three.
const codec_format =
    \\Format := [Default].{
    \\    rename_field : Format, Str -> Str
    \\    rename_field = |_f, name| name
    \\
    \\    encode_record : U64, U64, (U64, (U64, Str, (U64 -> Try(U64, [])) -> Try(U64, [])) -> Try(U64, [])) -> Try(U64, [])
    \\    encode_record = |state, _n, write_fields| {
    \\        finished = write_fields(state + 1, |field_state, name, write_value| write_value(field_state + name.count_utf8_bytes()))?
    \\        Ok(finished + 2)
    \\    }
    \\
    \\    encode_str : Str, U64 -> Try(U64, [])
    \\    encode_str = |value, state| Ok(state + value.count_utf8_bytes())
    \\}
    \\
;

// A stage that prints a `Derived` node whole, subject type included, because
// the subject is the part a codec translator reads.
const codec_stage =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Str.join_with(Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}").append(Stage.node(Code.ir(code))), " ; ")
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\        Param(name, _m) => "param ${name}"
    \\        Lit(_l, _m) => "lit"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        MakeTag(name, _p, _m) => "tag ${name}"
    \\        Derived(name, subject, args, _m) => "derived ${name} of ${Stage.ty(subject)}(${Str.join_with(args.map(Stage.node), ", ")})"
    \\        _ => "other"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Record(fields) => "{ ${Str.join_with(fields.map(|f| "${f.name} : ${Stage.ty(f.ty)}"), ", ")} }"
    \\        Named(name, _backing) => name
    \\        Str => "Str"
    \\        _ => "?"
    \\    }
    \\}
    \\
;

// A derived codec is curried: the body constructs the encoder and then runs
// it. Applying a function value has no node, so the two halves describe as one
// `Derived` the stage expands, with the constructor's arguments before the
// applied ones. The subject carries the shape the compiler derived against.
const staged_derived_codec = codec_stage ++ codec_format ++
    \\encode : value -> Try(U64, [])
    \\    where [
    \\        value.encoder_for : Format -> (value, U64 -> Try(U64, [])),
    \\    ]
    \\encode = |value| {
    \\    Shape : value
    \\    encode_value = Shape.encoder_for(Format.Default)
    \\    encode_value(value, 0)
    \\}
    \\
    \\emit : { a : Str } -> Try(U64, [])
    \\emit = |r| encode(r)
    \\main = Stage.describe(emit)
;

// One constrained body, two instantiations: the compiler derives the encoder
// for a record and the author wrote one for the nominal. The body names its own
// evidence param either way, so the call that fixed the type is the only thing
// that can tell the two apart.
const staged_codec_origin = codec_stage ++ codec_format ++
    \\Token := { raw : Str }.{
    \\    encoder_for : Format -> (Token, U64 -> Try(U64, []))
    \\    encoder_for = |_f| |token, state| Format.encode_str(token.raw, state)
    \\}
    \\
    \\construct : value -> (value, U64 -> Try(U64, []))
    \\    where [
    \\        value.encoder_for : Format -> (value, U64 -> Try(U64, [])),
    \\    ]
    \\construct = |_value| {
    \\    Shape : value
    \\    Shape.encoder_for(Format.Default)
    \\}
    \\
    \\by_shape : { a : Str } -> ({ a : Str }, U64 -> Try(U64, []))
    \\by_shape = |r| construct(r)
    \\
    \\by_hand : Token -> (Token, U64 -> Try(U64, []))
    \\by_hand = |t| construct(t)
    \\main = "${Stage.describe(by_shape)} | ${Stage.describe(by_hand)}"
;

// A codec the author wrote is a curried definition like any other, so running
// one describes as the `Call` a translator resolves against a row, where a
// derived one describes as the `Derived` a stage expands. Both carry the same
// arguments in the same order, which is what lets one translator read either.
const staged_codec_applied = codec_stage ++ codec_format ++
    \\Token := { raw : Str }.{
    \\    encoder_for : Format -> (Token, U64 -> Try(U64, []))
    \\    encoder_for = |_f| |token, state| Format.encode_str(token.raw, state)
    \\}
    \\
    \\encode : value -> Try(U64, [])
    \\    where [
    \\        value.encoder_for : Format -> (value, U64 -> Try(U64, [])),
    \\    ]
    \\encode = |value| {
    \\    Shape : value
    \\    Shape.encoder_for(Format.Default)(value, 0)
    \\}
    \\
    \\by_shape : { a : Str } -> Try(U64, [])
    \\by_shape = |r| encode(r)
    \\
    \\by_hand : Token -> Try(U64, [])
    \\by_hand = |t| encode(t)
    \\main = "${Stage.describe(by_shape)} | ${Stage.describe(by_hand)}"
;

const staged_record_field = stage ++
    \\Point := { x : F32, y : F32 }
    \\
    \\lift : Point -> F32
    \\lift = |p| p.x + p.y
    \\
    \\Lifted :: {}.{
    \\    describe : Code(Point -> F32) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\}
    \\main = Lifted.describe(lift)
;

// A record a staged function takes arrives as a checked record type extended by
// another, so a walk that reads one link describes one field. The stage counts
// what it was handed and looks for every name, which is order-free: the order
// the fields arrive in is the solver's.
const staged_record_parameter =
    \\Shape :: {}.{
    \\    fields : Code(f) -> Str
    \\    fields = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.labels(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    labels : Code.Ty -> Str
    \\    labels = |ty| match ty {
    \\        Record(fs) => {
    \\            names = fs.map(|f| f.name)
    \\            found = ["x", "y", "z"].keep_if(|want| names.contains(want))
    \\            "${names.len().to_str()} of ${found.len().to_str()}"
    \\        }
    \\        _ => "not a record"
    \\    }
    \\}
    \\
    \\lift : { x : F32, y : F32, z : F32 } -> F32
    \\lift = |p| p.x + p.y + p.z
    \\main = Shape.fields(lift)
;

// A tag union names its variants and each variant's payload types. The
// variants arrive in name order, which is the order the compiler holds them in,
// so the expected string is order-free only in the sense that it is fixed.
const staged_tag_union_type =
    \\Shape :: {}.{
    \\    variants : Code(f) -> Str
    \\    variants = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.ty(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(Shape.variant), ", ")}]"
    \\        _ => "not a tag union"
    \\    }
    \\
    \\    variant : { name : Str, payloads : List(Code.Ty) } -> Str
    \\    variant = |v| "${v.name}/${v.payloads.len().to_str()}"
    \\}
    \\
    \\pick : [Red, Green(F32, F32), Blue] -> F32
    \\pick = |_c| 1.0
    \\main = Shape.variants(pick)
;

// A recursive nominal describes as a `Named` whose backing reaches back to it
// as a `Recursive` of the same name, so the description stays a finite tree.
const staged_recursive_type =
    \\Shape :: {}.{
    \\    param : Code(f) -> Str
    \\    param = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.ty(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Named(name, backing) => "${name} = ${Shape.ty(backing)}"
    \\        Recursive(name) => "^${name}"
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(Shape.variant), ", ")}]"
    \\        F32 => "F32"
    \\        _ => "other"
    \\    }
    \\
    \\    variant : { name : Str, payloads : List(Code.Ty) } -> Str
    \\    variant = |v| "${v.name}(${Str.join_with(v.payloads.map(Shape.ty), ", ")})"
    \\}
    \\
    \\Tree := [Leaf, Node(Tree, Tree)]
    \\
    \\depth : Tree -> F32
    \\depth = |t| match t {
    \\    Leaf => 1.0
    \\    Node(_l, _r) => 2.0
    \\}
    \\main = Shape.param(depth)
;

// A recursive nominal with a type parameter. The declaration's backing is one
// template every use shares, so the walk recognises the return by the nominal
// and what this use fixed its variables to rather than by the checked id.
const staged_recursive_parametric_type =
    \\Shape :: {}.{
    \\    param : Code(f) -> Str
    \\    param = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.ty(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Named(name, backing) => "${name} = ${Shape.ty(backing)}"
    \\        Recursive(name) => "^${name}"
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(Shape.variant), ", ")}]"
    \\        F32 => "F32"
    \\        U16 => "U16"
    \\        _ => "other"
    \\    }
    \\
    \\    variant : { name : Str, payloads : List(Code.Ty) } -> Str
    \\    variant = |v| "${v.name}(${Str.join_with(v.payloads.map(Shape.ty), ", ")})"
    \\}
    \\
    \\Tree(a) := [Leaf, Node(Tree(a), a)]
    \\
    \\depth : Tree(U16) -> F32
    \\depth = |t| match t {
    \\    Leaf => 1.0
    \\    Node(_l, _v) => 2.0
    \\}
    \\main = Shape.param(depth)
;

// The same nominal reaching itself at other type arguments. `Chain(F32)` holds
// a `Chain(U16)`, which is a different type and takes a `Named` of its own, so
// the `Recursive` under it names the nearest enclosing `Named` and means it.
const staged_recursive_changing_argument =
    \\Shape :: {}.{
    \\    param : Code(f) -> Str
    \\    param = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.ty(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Named(name, backing) => "${name} = ${Shape.ty(backing)}"
    \\        Recursive(name) => "^${name}"
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(Shape.variant), ", ")}]"
    \\        F32 => "F32"
    \\        U16 => "U16"
    \\        _ => "other"
    \\    }
    \\
    \\    variant : { name : Str, payloads : List(Code.Ty) } -> Str
    \\    variant = |v| "${v.name}(${Str.join_with(v.payloads.map(Shape.ty), ", ")})"
    \\}
    \\
    \\Chain(a) := [End, Link(a, Chain(U16))]
    \\
    \\depth : Chain(F32) -> F32
    \\depth = |c| match c {
    \\    End => 1.0
    \\    Link(_v, _rest) => 2.0
    \\}
    \\main = Shape.param(depth)
;

// `children` hands back a node's immediate sub-expressions whatever kind it
// is, so a pass with nothing to say about kinds walks with it instead of
// writing an arm per kind. A guard is a child of its `Match`, and a loop's
// source, body and carried initial are children of its `For`.
const staged_ir_children =
    \\Shape :: {}.{
    \\    walk : Code(f) -> Str
    \\    walk = |code| {
    \\        root = Code.ir(code)
    \\        "${Shape.count(root).to_str()} nodes, ${Str.join_with(Shape.calls(root), " ")}"
    \\    }
    \\
    \\    count : Code.Ir -> U64
    \\    count = |node| 1 + node.children().map(Shape.count).sum()
    \\
    \\    calls : Code.Ir -> List(Str)
    \\    calls = |node| {
    \\        here = match node {
    \\            Call(name, _a, _m) => [name]
    \\            _ => []
    \\        }
    \\        List.concat(here, node.children().join_map(Shape.calls))
    \\    }
    \\}
    \\
    \\grade : U16, F32 -> F32
    \\grade = |n, t| {
    \\    var $total = t * 2.0
    \\    for step in [1.0, 2.0] {
    \\        $total = $total + step
    \\    }
    \\    match n {
    \\        0 => $total
    \\        v if v.min(9) > 3 => $total.min(v.to_f32())
    \\        _ => $total + 1.0
    \\    }
    \\}
    \\main = Shape.walk(grade)
;

// `numeric` answers the question an operation site asks about a number, and
// `name` spells a type the way Roc spells it, so a translator refusing one
// says which.
const staged_ty_questions =
    \\Shape :: {}.{
    \\    ask : Code(f) -> Str
    \\    ask = |code| match Code.ir(code) {
    \\        Lambda(params, _body, _m) => Str.join_with(params.map(|p| Shape.about(p.ty)), " | ")
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    about : Code.Ty -> Str
    \\    about = |t| match t.numeric() {
    \\        Ok(number) => {
    \\            kind = match number.kind {
    \\                Int => "int"
    \\                Frac => "frac"
    \\                Fixed => "fixed"
    \\            }
    \\            sign = if number.signed "signed" else "unsigned"
    \\            "${t.name()} ${kind} ${number.bits.to_str()} ${sign}"
    \\        }
    \\        Err(NotNumeric) => "${t.name()} not numeric"
    \\    }
    \\}
    \\
    \\Point := { x : F32, y : F32 }
    \\
    \\place : F32, U16, Dec, Point, List(Str), [Red, Green(U8)] -> F32
    \\place = |a, _b, _c, _d, _e, _f| a
    \\main = Shape.ask(place)
;

/// A stage that prints where a value moves to a wider tag union, with the
/// union it leaves and the union it reaches.
const widen_stage =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_p, body, _m) => Stage.node(body)
    \\        Param(name, _m) => name
    \\        MakeTag(name, _p, m) => "${name} : ${Stage.ty(m.ty)}"
    \\        Widen(inner, m) => "widen (${Stage.node(inner)}) to ${Stage.ty(m.ty)}"
    \\        Match(subject, branches, _m) =>
    \\            "match ${Stage.node(subject)} { ${Str.join_with(branches.map(|b| Stage.node(b.value)), " ")} }"
    \\        _ => "other"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        TagUnion(variants) => "[${Str.join_with(variants.map(|v| v.name), " ")}]"
    \\        _ => "ty"
    \\    }
    \\}
    \\
;

// Every use of a top-level value reads it at one union, the widest any use
// reads (design.md "Row Coercion Primitive"), so the value folds into the use
// at that union and nothing widens it.
const staged_widened_value = widen_stage ++
    \\mode = Fast
    \\
    \\pick : F32 -> F32
    \\pick = |x| match mode {
    \\    Fast => x
    \\    Slow => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// A function whose body forwards its closed input into the union its
// annotation leaves open widens it inside its own body, into its result. The
// call hands back that result, which the caller reads as it is.
const staged_widened_call = widen_stage ++
    \\keep : [Small, Big] -> [Small, Big]
    \\keep = |size| size
    \\
    \\pick : F32 -> F32
    \\pick = |x| match keep(if x < 1.0 Small else Big) {
    \\    Small => x
    \\    Big => 2.0
    \\    Huge => 3.0
    \\}
    \\main = Stage.describe(pick)
;

/// A stage that prints a whole `match`: its subject, its patterns, its guards
/// and its branch values, so every part of a described branch is in the output.
const match_stage =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_p, body, _m) => Stage.node(body)
    \\        Param(name, _m) => name
    \\        Local(name, _m) => name
    \\        Lit(l, _m) => Stage.lit(l)
    \\        MakeTag(name, payloads, _m) => "${name}(${Str.join_with(payloads.map(Stage.node), " ")})"
    \\        Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\        MakeTuple(items, _m) => "(${Str.join_with(items.map(Stage.node), " ")})"
    \\        Field(record, name, _m) => "${Stage.node(record)}.${name}"
    \\        Match(subject, branches, _m) =>
    \\            "match ${Stage.node(subject)} { ${Str.join_with(branches.map(Stage.branch), " ")} }"
    \\        If(cond, yes, no, _m) => "if ${Stage.node(cond)} then ${Stage.node(yes)} else ${Stage.node(no)}"
    \\        Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
    \\        _ => "other"
    \\    }
    \\
    \\    lit : Code.Lit -> Str
    \\    lit = |l| match l {
    \\        Bool(v) => if v "True" else "False"
    \\        Int(v, _t) => v.to_str()
    \\        Frac(v, _t) => v.to_str()
    \\        Fixed(v) => v.to_str()
    \\        Str(v) => "'${v}'"
    \\    }
    \\
    \\    branch : Code.Branch -> Str
    \\    branch = |b| {
    \\        guard = match b.guard {
    \\            NoGuard => ""
    \\            Guard(g) => " if ${Stage.node(g)}"
    \\        }
    \\        "${Str.join_with(b.patterns.map(Stage.pattern), " | ")}${guard} => ${Stage.node(b.value)}"
    \\    }
    \\
    \\    pattern : Code.Pattern -> Str
    \\    pattern = |p| match p {
    \\        Bind(name, _m) => name
    \\        Anything(_m) => "_"
    \\        Variant(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.pattern), " ")})"
    \\        PatLit(l, _m) => Stage.lit(l)
    \\        PatTuple(items, _m) => "(${Str.join_with(items.map(Stage.pattern), " ")})"
    \\        PatRecord(fs, _m) => "{${Str.join_with(fs.map(|f| "${f.name}: ${Stage.pattern(f.pattern)}"), " ")}}"
    \\        PatAs(inner, name, _m) => "${Stage.pattern(inner)} as ${name}"
    \\        PatGuard(inner, cond, _m) => "${Stage.pattern(inner)} when ${Stage.node(cond)}"
    \\        PatList(items, _m) => "[${Str.join_with(items.map(Stage.pattern), " ")}]"
    \\        PatListRest(before, rest, after, _m) =>
    \\            "[${Str.join_with(before.map(Stage.pattern), " ")} ${Stage.bound(rest)} ${Str.join_with(after.map(Stage.pattern), " ")}]"
    \\        PatStr(prefix, steps, end, _m) => {
    \\            tail = match end {
    \\                Exact => ""
    \\                Tail => ".."
    \\            }
    \\            "'${prefix}'${Str.join_with(steps.map(|s| "${Stage.bound(s.capture)}'${s.delimiter}'"), "")}${tail}"
    \\        }
    \\    }
    \\
    \\    bound : [Ignored, Named(Str)] -> Str
    \\    bound = |b| match b {
    \\        Ignored => ".."
    \\        Named(name) => "..${name}"
    \\    }
    \\}
    \\
;

// A `match` over a tag union, with everything a branch can carry: an
// alternative, a guard, a payload binding read in the branch value, and a
// wildcard payload.
const staged_match = match_stage ++
    \\Color := [Red, Green(F32), Blue]
    \\
    \\shade : Color -> F32
    \\shade = |c| match c {
    \\    Red | Blue => 1.0
    \\    Green(v) if v > 0.0 => v
    \\    Green(_) => 0.0
    \\}
    \\main = Stage.describe(shade)
;

// A literal pattern, a tuple pattern and a record pattern, each with a binder
// beside it, so the shape of every pattern node is in one output.
const staged_match_patterns = match_stage ++
    \\pick : { a : U8, b : U8 } -> U8
    \\pick = |r| match r {
    \\    { a: 0, b } => b
    \\    { a, b: _ } => a
    \\}
    \\main = Stage.describe(pick)
;

// Constructing a tag, and a Bool, which is the one tag union with a literal.
const staged_make_tag = match_stage ++
    \\Color := [Red, Green(F32), Blue]
    \\
    \\paint : F32 -> Color
    \\paint = |x| Color.Green(x)
    \\main = Stage.describe(paint)
;

// A recursive nominal is a value like any other once its type describes: the
// body builds one and matches one, and the payload the match binds is itself
// a `Tree`.
const staged_recursive_value = match_stage ++
    \\Tree := [Leaf, Node(Tree, Tree)]
    \\
    \\grow : Tree -> Tree
    \\grow = |t| match t {
    \\    Leaf => Tree.Node(Tree.Leaf, Tree.Leaf)
    \\    Node(l, _r) => Tree.Node(l, t)
    \\}
    \\main = Stage.describe(grow)
;

// `and` short-circuits through Bool's tags, so it describes as the `if` the
// compiler turns it into, with `False` as an ordinary Bool literal.
const staged_and = match_stage ++
    \\band : F32 -> Bool
    \\band = |x| x > 1.0 and x < 2.0
    \\main = Stage.describe(band)
;

/// A stage that prints the literals it meets, so a folded compile-time
/// argument is visible in the output rather than only its shape.
const literal_stage =
    \\Stage :: {}.{
    \\    describe : Code(F32 -> F32) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir|
    \\        match ir {
    \\            Lambda(_params, body, _m) => "lambda -> ${Stage.node(body)}"
    \\            Param(name, _m) => "param ${name}"
    \\            Lit(l, _m) => match l {
    \\                Int(value, _t) => value.to_str()
    \\                Frac(value, _t) => value.to_str()
    \\                Fixed(value) => value.to_str()
    \\                Bool(value) => if value "True" else "False"
    \\                Str(value) => value
    \\            }
    \\            Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
    \\            Local(name, _m) => "local ${name}"
    \\            Let(name, value, body, _m) => "let ${name} = ${Stage.node(value)} in ${Stage.node(body)}"
    \\            Unary(op, value, _m) => "${op} ${Stage.node(value)}"
    \\            Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
    \\            Field(record, name, _m) => "${Stage.node(record)}.${name}"
    \\            Index(_r, _i, _m) => "index"
    \\            MakeRecord(fields, _m) => "{${Str.join_with(fields.map(|f| "${f.name}: ${Stage.node(f.value)}"), ", ")}}"
    \\            MakeTuple(elems, _m) => "(${Str.join_with(elems.map(Stage.node), ", ")})"
    \\            MakeList(elems, _m) => "[${Str.join_with(elems.map(Stage.node), ", ")}]"
    \\            If(cond, yes, no, _m) => "if ${Stage.node(cond)} then ${Stage.node(yes)} else ${Stage.node(no)}"
    \\            MakeTag(name, payloads, _m) => "${name}(${Str.join_with(payloads.map(Stage.node), ", ")})"
    \\            Match(_s, _b, _m) => "match"
    \\            Crash(_message, _m) => "crash"
    \\            Derived(name, _s, _a, _m) => "derived ${name}"
    \\        }
    \\}
    \\
;

// A function that returns a `Code` is a template: the compiler calls it and
// writes the arguments into the description, so the parameter the template
// took is a literal by the time the stage reads the body.
const staged_template = literal_stage ++
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |factor| |x| x * factor
    \\main = Stage.describe(scaled(3.0.F32))
;

// One template, two calls, two descriptions. This is what makes a template
// worth having: the threshold is in the description rather than in the source.
const staged_template_twice = literal_stage ++
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |factor| |x| x * factor
    \\main = "${Stage.describe(scaled(2.0.F32))} | ${Stage.describe(scaled(7.0.F32))}"
;

// A template takes as many compile-time arguments as it likes, and one it never
// names is simply absent from the description.
const staged_template_many = literal_stage ++
    \\shifted : F32, Str, F32 -> Code(F32 -> F32)
    \\shifted = |factor, _label, offset| |x| x * factor + offset
    \\main = Stage.describe(shifted(2.0.F32, "unused", 5.0.F32))
;

// A list a staged body writes is a `MakeList`, which is also what lets a
// template take one: a compile-time argument is written into the description,
// so every part of it has to be something the `Ir` can hold.
const staged_list = literal_stage ++
    \\scaled : List(F32) -> Code(F32 -> F32)
    \\scaled = |steps| |x| x * steps.len().to_f32()
    \\main = Stage.describe(scaled([2.0.F32, 4.0.F32]))
;

// A record argument arrives whole, and a field read of it describes as a
// `Field` over the record the call fixed.
const staged_record_argument = literal_stage ++
    \\shifted : { dx : F32, dy : F32 } -> Code(F32 -> F32)
    \\shifted = |by| |x| x * by.dx
    \\main = Stage.describe(shifted({ dx: 3.0.F32, dy: 0.5.F32 }))
;

// A plain call to a definition of this module is described by name, and the
// callee's body is not written into the description. The name is qualified by
// the module that defines it, because one table holds the definitions of every
// module a description reaches.
const staged_plain_call = literal_stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x) + step(step(x))
    \\main = Stage.describe(bump)
;

/// A stage that prints the definition table beside the body, so what a `Call`
/// resolves to is visible rather than only the name that reaches it.
const table_stage = literal_stage ++
    \\Table :: {}.{
    \\    describe : Code(F32 -> F32) -> Str
    \\    describe = |code| {
    \\        rows = Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}")
    \\        "${Str.join_with(rows, " ; ")} || ${Stage.node(Code.ir(code))}"
    \\    }
    \\}
    \\
;

// The callee's own description arrives beside the root, so a translator emits
// one function per definition rather than resolving a name it has nothing for.
// `step` is called three times and described once.
const staged_call_table = table_stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x) + step(step(x))
    \\main = Table.describe(bump)
;

// A callee comes before its caller, so a target that declares a function
// before it calls one emits the table in order.
const staged_call_chain = table_stage ++
    \\inner : F32 -> F32
    \\inner = |x| x + 1.0
    \\middle : F32 -> F32
    \\middle = |x| inner(x) * 2.0
    \\outer : F32 -> F32
    \\outer = |x| middle(x) - inner(x)
    \\main = Table.describe(outer)
;

// Two sites reaching one callee each get a row for it, and the walk describes
// that callee once.
const staged_call_shared = table_stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x)
    \\twice : F32 -> F32
    \\twice = |x| step(step(x))
    \\main = "${Table.describe(bump)} | ${Table.describe(twice)}"
;

// The described function is a row of its own table only when it calls itself,
// because that is the one description whose `Call` names it.
const staged_recursive_table = table_stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 countdown(x - 1.0) else 0.0
    \\main = Table.describe(countdown)
;

// Naming the callee rather than inlining it is what lets a recursive function
// describe at all: the walk writes one `Call` and stops.
const staged_recursive_call = literal_stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 countdown(x - 1.0) else 0.0
    \\main = Stage.describe(countdown)
;

// A derived `==` over a tag union is the match that comparison is: the
// operands paired, one branch per variant, and a `_` for every pair that
// disagrees on the variant. A payload is bound because no node reaches inside
// a variant, and the compiler names the binder because no source holds one.
const staged_derived_eq = match_stage ++
    \\same : [Red, Green(U8)], [Red, Green(U8)] -> Bool
    \\same = |a, b| a == b
    \\main = Stage.describe(same)
;

// The nominal's own name reaches the patterns the comparison writes, the way
// it reaches a pattern someone wrote, so a translator that keys on `Color`
// finds it.
const staged_derived_eq_nominal =
    \\Shape :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(_p, body, _m) => Shape.node(body)
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Match(_s, branches, _m) => Str.join_with(branches.map(Shape.branch), " ")
    \\        _ => "other"
    \\    }
    \\
    \\    branch : Code.Branch -> Str
    \\    branch = |b| Str.join_with(b.patterns.map(|p| Shape.ty(p.pattern_ty())), " ")
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Named(name, _backing) => name
    \\        Tuple(items) => "(${Str.join_with(items.map(Shape.ty), " ")})"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\Color := [Red, Green].{
    \\    is_eq : _
    \\}
    \\
    \\same : Color, Color -> Bool
    \\same = |a, b| a == b
    \\main = Shape.describe(same)
;

// `List.get` returns `Try(a, [OutOfBounds]*)`, and the checker closes that
// error row at the call without rewriting it to `[]`: it marks the variable it
// solved instead. The walk reads the mark, so indexing a list describes.
const staged_list_index =
    \\Shape :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(_p, body, _m) => Shape.node(body)
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Match(subject, _b, _m) => "${Shape.node(subject)} : ${Shape.ty(subject.node_ty())}"
    \\        Call(name, _a, _m) => name
    \\        _ => "other"
    \\    }
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Opaque(name, args) => "${name}(${Str.join_with(args.map(Shape.ty), ", ")})"
    \\        TagUnion(vs) => "[${Str.join_with(vs.map(|v| v.name), ", ")}]"
    \\        U64 => "U64"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\first : List(U64) -> U64
    \\first = |xs| match xs.get(0) {
    \\    Ok(v) => v
    \\    Err(_e) => 0
    \\}
    \\main = Shape.describe(first)
;

// A reified function that hands back a nullary tag, read by a stage that
// discards both of the `Lambda` payloads. Discarding them is what makes the
// reader assign the whole `List(Param)` across a layout boundary, so the arm
// has to stay payload-free for this case to cover what it covers.
const staged_nullary_tag_result =
    \\Shape :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(_p, _b, _m) => "lambda"
    \\        _ => "not a lambda"
    \\    }
    \\}
    \\
    \\probe : U64 -> [Red]
    \\probe = |_n| Red
    \\main = Shape.describe(probe)
;

// An empty list and an empty record are the aggregate each node already
// builds, with nothing in it.
const staged_empty_aggregate =
    \\Shape :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| match Code.ir(code) {
    \\        Lambda(_p, body, _m) => Shape.node(body)
    \\        _ => "not a lambda"
    \\    }
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        MakeList(items, _m) => "list of ${items.len().to_str()}"
    \\        MakeRecord(fields, _m) => "record of ${fields.len().to_str()}"
    \\        _ => "other"
    \\    }
    \\}
    \\
    \\no_items : U64 -> List(U64)
    \\no_items = |_n| []
    \\
    \\no_fields : U64 -> {}
    \\no_fields = |_n| {}
    \\main = "${Shape.describe(no_items)} ; ${Shape.describe(no_fields)}"
;

// A top-level value read from a staged body is the value it holds. The name
// never reaches the description, so a translator has no name to resolve and
// the reified body stays closed over nothing.
const staged_top_level_constant = literal_stage ++
    \\threshold = 2.0.F32
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * threshold
    \\main = Stage.describe(scale)
;

// A value another module exports folds the same way, read through that
// module's own tables.
const staged_imported_constant = literal_stage ++
    \\import Limits
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * Limits.ceiling
    \\main = Stage.describe(scale)
;

// An aggregate folds whole, so a field read of a top-level record describes as
// a `Field` over the record the definition wrote.
const staged_constant_record = literal_stage ++
    \\settings = { gain: 3.0.F32, bias: 0.5.F32 }
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * settings.gain
    \\main = Stage.describe(scale)
;

// A name as a template argument is the value it holds, which is the same
// resolution step read from the other refusal.
const staged_constant_template_argument = literal_stage ++
    \\factor = 4.0.F32
    \\
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |k| |x| x * k
    \\main = Stage.describe(scaled(factor))
;

// `??` canonicalizes to a match whose `Ok` branch binds a name the compiler
// spelled, and the `Ir` names its bindings. The walk gives that binder a name
// of its own, so the branch describes instead of stopping the walk.
const staged_default_operand = match_stage ++
    \\pick : Try(F32, [Bad]), F32 -> F32
    \\pick = |t, fallback| t ?? fallback
    \\main = Stage.describe(pick)
;

// `p as name` keeps the name beside the pattern it renames rather than moving
// it into the branch value, because that is where the author wrote it.
const staged_as_pattern = match_stage ++
    \\Pair := { a : F32, b : F32 }
    \\
    \\first : Pair -> F32
    \\first = |p| match p {
    \\    Pair.{ a: _, b: _ } as whole => whole.a
    \\}
    \\main = Stage.describe(first)
;

// A literal written against the author's own type is the conversion the
// checker wrote, named. The operand is the number or the text the author
// wrote, because the `Num.Numeral` the conversion declares is an opaque a
// translator has no reason to model.
const staged_custom_numeral = literal_stage ++
    \\Meters := { m : F32 }.{
    \\    from_numeral : Numeral -> Try(Meters, [InvalidNumeral(Str)])
    \\    from_numeral = |n| match F32.from_numeral(n) {
    \\        Ok(v) => Ok({ m: v })
    \\        Err(e) => Err(e)
    \\    }
    \\    scale : Meters, F32 -> F32
    \\    scale = |me, f| me.m * f
    \\}
    \\
    \\stretch : F32 -> F32
    \\stretch = |x| 3.0.Meters.scale(x)
    \\main = Stage.describe(stretch)
;

const staged_custom_quote = literal_stage ++
    \\Name := { text : Str }.{
    \\    from_quote : Str -> Try(Name, [BadQuotedBytes(Str)])
    \\    from_quote = |s| Ok({ text: s })
    \\    width : Name, F32 -> F32
    \\    width = |n, f| if n.text.is_empty() 0.0.F32 else f
    \\}
    \\
    \\measure : F32 -> F32
    \\measure = |x| "hi".Name.width(x)
    \\main = Stage.describe(measure)
;

// A literal pattern of the author's own type is a binder and a condition, and
// the condition stays on the alternative that owns it. `7 | 8` is what a
// branch-level guard could not hold: two conditions, each reading a binder
// only its own alternative binds.
const staged_custom_literal_pattern = match_stage ++
    \\Count := { n : U32 }.{
    \\    from_numeral : Numeral -> Try(Count, [InvalidNumeral(Str)])
    \\    from_numeral = |v| match U32.from_numeral(v) {
    \\        Ok(u) => Ok({ n: u })
    \\        Err(e) => Err(e)
    \\    }
    \\    is_eq : Count, Count -> Bool
    \\    is_eq = |a, b| a.n == b.n
    \\}
    \\
    \\pick : Count, F32 -> F32
    \\pick = |c, f| match c {
    \\    7 | 8 => f
    \\    _ => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// A plain call to a function the compiler provides takes the name a method
// call on the same builtin takes, so the two spellings describe as one `Call`.
// `plain` and `method` are the same function written two ways, and the stage
// prints one string twice.
const staged_builtin_call = literal_stage ++
    \\plain : F32 -> F32
    \\plain = |x| if Str.is_empty(F32.to_str(x)) x else x
    \\method : F32 -> F32
    \\method = |x| if x.to_str().is_empty() x else x
    \\main = "${Stage.describe(plain)} | ${Stage.describe(method)}"
;

// A builtin is named and nothing more: no row goes into the table, because a
// translator resolves the name against what its own target provides rather
// than against a body written in Roc.
const staged_builtin_call_table = table_stage ++
    \\pick : F32 -> F32
    \\pick = |x| if Str.is_empty(F32.to_str(x)) x else x
    \\main = Table.describe(pick)
;

// A string literal of more than one segment is the concatenation it is: one
// `concat` per join, named the way the same call written by hand is named. An
// empty segment joins nothing, so `"${s}"` describes as the name alone.
const staged_interpolation = literal_stage ++
    \\parts : F32 -> F32
    \\parts = |x| if Str.is_empty("p${x.to_str()}q") x else x
    \\only : F32 -> F32
    \\only = |x| if Str.is_empty("${x.to_str()}") x else x
    \\main = "${Stage.describe(parts)} | ${Stage.describe(only)}"
;

// An interpolated literal of the author's own type applies the assembler its
// `from_interpolation` hands back while the compiler runs. That assembler is a
// function value, which a first-order description has no node to apply, so
// the walk refuses it.
const staged_custom_interpolation = literal_stage ++
    \\Label := { text : Str }.{
    \\    from_interpolation : List(Str) -> Try((List(Str) -> Label), [InvalidInterpolation(Str)])
    \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| { text: assemble(values) })
    \\    width : Label, F32 -> F32
    \\    width = |l, f| if l.text.is_empty() 0.0.F32 else f
    \\}
    \\
    \\mark : F32 -> F32
    \\mark = |x| "a${x.to_str()}b".Label.width(x)
    \\main = Stage.describe(mark)
;

/// A stage that prints what a record type says about the presence of each of
/// its fields, and names a read of a field that may be absent.
const presence_stage =
    \\Stage :: {}.{
    \\    describe : Code(F32 -> F32) -> Str
    \\    describe = |code| Stage.node(Code.ir(code))
    \\
    \\    ty : Code.Ty -> Str
    \\    ty = |t| match t {
    \\        Record(fields) => "{${Str.join_with(fields.map(|f| "${f.name}${match f.presence { Required => "" Optional => "?" }}"), " ")}}"
    \\        Opaque(name, args) => "${name}(${Str.join_with(args.map(Stage.ty), " ")})"
    \\        TagUnion(variants) => "[${Str.join_with(variants.map(|v| v.name), " ")}]"
    \\        F32 => "F32"
    \\        _ => "ty"
    \\    }
    \\
    \\    node : Code.Ir -> Str
    \\    node = |ir| match ir {
    \\        Lambda(_p, body, _m) => "lambda -> ${Stage.node(body)}"
    \\        Param(name, _m) => name
    \\        Local(name, _m) => name
    \\        Let(name, value, body, _m) => "let ${name} = ${Stage.node(value)} : ${Stage.ty(value.node_ty())} in ${Stage.node(body)}"
    \\        Field(record, name, _m) => "${Stage.node(record)}.${name}"
    \\        OptField(record, name, m) => "${Stage.node(record)}.?${name} : ${Stage.ty(m.ty)}"
    \\        MakeRecord(fields, _m) => "{${Str.join_with(fields.map(|f| "${f.name}: ${Stage.node(f.value)}"), " ")}}"
    \\        Match(subject, branches, _m) => "match ${Stage.node(subject)} { ${Str.join_with(branches.map(|b| Stage.node(b.value)), " ")} }"
    \\        Lit(_l, _m) => "lit"
    \\        _ => "node"
    \\    }
    \\}
    \\
;

// A record update has no node of its own. Every field of the result is either
// one the update wrote or one read out of the subject, and the subject is a
// name here, so it is read again rather than bound.
const staged_record_update = literal_stage ++
    \\Pt : { x : F32, y : F32 }
    \\move : F32 -> F32
    \\move = |v| {
    \\    base : Pt
    \\    base = { x: v, y: 1.0 }
    \\    moved = { ..base, y: 2.0 }
    \\    moved.x + moved.y
    \\}
    \\main = Stage.describe(move)
;

// A subject that is not a name is read once per field the update did not
// write, so the walk binds it to a name of its own first.
const staged_record_update_binds = literal_stage ++
    \\move : F32 -> F32
    \\move = |v| {
    \\    moved = { ..{ x: v, y: 1.0 }, y: 2.0 }
    \\    moved.x + moved.y
    \\}
    \\main = Stage.describe(move)
;

// A field the literal leaves unset is left out: `MakeRecord` lists what the
// literal sets, and the type beside it says the field may be absent.
const staged_unset_field = presence_stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\pick : F32 -> F32
    \\pick = |v| {
    \\    c : Cfg
    \\    c = { a: v, b: _ }
    \\    c.a
    \\}
    \\main = Stage.describe(pick)
;

// A `.?` read hands back the `Try` the value sits in rather than the value,
// so it is a node of its own and carries that `Try` as its type.
const staged_optional_field = presence_stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\pick : F32 -> F32
    \\pick = |v| {
    \\    c : Cfg
    \\    c = { a: v }
    \\    match c.?b {
    \\        Ok(f) => f
    \\        Err(_) => v
    \\    }
    \\}
    \\main = Stage.describe(pick)
;

// A `..` that binds nothing adds no entry to the record pattern: the fields it
// stands for are exactly the ones the entries beside it do not name.
const staged_record_rest = match_stage ++
    \\pick : { x : F32, y : F32 } -> F32
    \\pick = |p| match p {
    \\    { x, .. } => x
    \\}
    \\main = Stage.describe(pick)
;

// An exact-length list pattern and one with a rest are two nodes, because a
// translator answers the two with a length test and a slice.
const staged_list_pattern = match_stage ++
    \\pick : List(F32) -> F32
    \\pick = |l| match l {
    \\    [a, b] => a - b
    \\    [a, .., b] => a + b
    \\    [a, .. as mid, b] => a * b
    \\    _ => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// A string pattern is transcribed: the text it starts with, one step per
// interpolation, and whether the last delimiter ends the string.
const staged_str_pattern = match_stage ++
    \\pick : Str -> Str
    \\pick = |s| match s {
    \\    "a${head}b${_}" => head
    \\    "${tail}z" => tail
    \\    _ => s
    \\}
    \\main = Stage.describe(pick)
;

/// Staging cases, consumed by the parallel runner through `eval_tests.zig`.
pub const tests = [_]TestCase{
    .{
        .name = "staging - a staged function's body becomes a description the stage reads",
        .source_kind = .module,
        .source = staged_binop,
        .expected = .{ .inspect_str = "\"lambda -> (param x times lit)\"" },
    },
    .{
        .name = "staging - a binding in the staged body survives as a Let",
        .source_kind = .module,
        .source = staged_let,
        .expected = .{ .inspect_str = "\"lambda -> let wave = (param x times lit) in (local wave plus local wave)\"" },
    },
    .{
        .name = "staging - a generic callee is one row per instantiation",
        .source_kind = .module,
        .source = staged_generic_instantiations,
        .expected = .{ .inspect_str = "\"Test.pick(F32, Str) ; Test.pick#1(F32, F32)\"" },
    },
    .{
        .name = "staging - a nested generic callee is keyed by the outer instantiation",
        .source_kind = .module,
        .source = staged_generic_nested,
        .expected = .{ .inspect_str = "\"Test.id(F32) ; Test.wrap(F32)\"" },
    },
    .{
        .name = "staging - a generic callee is fixed through a record parameter",
        .source_kind = .module,
        .source = staged_generic_record,
        .expected = .{ .inspect_str = "\"Test.field({v: F32}) ; Test.field#1({v: Str})\"" },
    },
    .{
        .name = "staging - a where-constrained callee names the type the call fixed",
        .source_kind = .module,
        .source = staged_generic_where,
        .expected = .{ .inspect_str = "\"Test.show = lambda -> Builtin.Num.F32.to_str(param v) | Test.plain = lambda -> Builtin.Num.F32.to_str(param v)\"" },
    },
    .{
        .name = "staging - a type-level statement in a block leaves no node behind",
        .source_kind = .module,
        .source = staged_type_statement,
        .expected = .{ .inspect_str = "\"lambda -> let k = (param x times lit) in (local k plus lit)\"" },
    },
    .{
        .name = "staging - a type dispatch names the type the instantiation fixed",
        .source_kind = .module,
        .source = staged_type_dispatch,
        .expected = .{ .inspect_str = "\"Token.tag_of = lambda -> other ; Test.name = lambda -> Token.tag_of(param fmt, param v) ; lambda -> Test.name(param t, tag Default)\"" },
    },
    .{
        .name = "staging - a method call names a row the way a plain call does",
        .source_kind = .module,
        .source = staged_method_definition,
        .expected = .{ .inspect_str = "\"Token.label = lambda -> param t.raw ; lambda -> Token.label(param t)\"" },
    },
    .{
        .name = "staging - a parametric nominal reads its backing at its type arguments",
        .source_kind = .module,
        .source = staged_parametric_nominal,
        .expected = .{ .inspect_str = "\"Crate([Empty(), Full(F32)]) => derived map of Crate([Empty(), Full(F32)])(param b, (v) -> (param v times lit))\"" },
    },
    .{
        .name = "staging - a function argument fixes the parameter it is passed for",
        .source_kind = .module,
        .source = staged_function_argument,
        .expected = .{ .inspect_str = "\"Test.double = (y) -> (param y times lit) ; Test.apply_to = (x) -> Test.double(param x) ; Test.triple = (y) -> (param y times lit) ; Test.apply_to#1 = (x) -> Test.triple(param x) ; (x) -> (Test.apply_to(param x) plus Test.apply_to#1(param x)) | Test.y = (y) -> (param y minus lit) ; Test.apply_to#2 = (x) -> Test.y(param x) ; (x) -> Test.apply_to#2(param x)\"" },
    },
    .{
        .name = "staging - a lambda a block bound is lifted into a row of its own",
        .source_kind = .module,
        .source = staged_local_lambda,
        .expected = .{ .inspect_str = "\"Test.step = (y) -> (param y times lit) ; (x) -> Test.step(param x) | Test.step#1 = (x, y) -> (param y times param x) ; (x) -> Test.step#1(param x, lit)\"" },
    },
    .{
        .name = "staging - a curried definition and the call that runs it are one row",
        .source_kind = .module,
        .source = staged_curried_call,
        .expected = .{ .inspect_str = "\"Test.scaler = (k, x) -> (param x times param k) ; (x) -> Test.scaler(lit, param x) | Test.scaler = (k, x) -> (param x times param k) ; (x) -> Test.scaler(lit, param x)\"" },
    },
    .{
        .name = "staging - a derived codec folds its construction and its use into one node",
        .source_kind = .module,
        .source = staged_derived_codec,
        .expected = .{ .inspect_str = "\"Test.encode = lambda -> derived encoder_for of { a : Str }(tag Default, param value, lit) ; lambda -> Test.encode(param r)\"" },
    },
    .{
        .name = "staging - a codec the author wrote describes as a call, not a Derived",
        .source_kind = .module,
        .source = staged_codec_origin,
        .expected = .{ .inspect_str = "\"Test.construct = lambda -> derived encoder_for of { a : Str }(tag Default) ; lambda -> Test.construct(param r) | Test.encode_str = lambda -> tag Ok ; Token.encoder_for = lambda -> lambda -> Test.encode_str(other, param state) ; Test.construct#1 = lambda -> Token.encoder_for(tag Default) ; lambda -> Test.construct#1(param t)\"" },
    },
    .{
        .name = "staging - a lambda inside the staged body is a Lambda where it stands",
        .source_kind = .module,
        .source = staged_nested_lambda,
        .expected = .{ .inspect_str = "\"(a) -> (b) -> (param a plus param b)\"" },
    },
    .{
        .name = "staging - a codec the author wrote is run through its own row",
        .source_kind = .module,
        .source = staged_codec_applied,
        .expected = .{ .inspect_str = "\"Test.encode = lambda -> derived encoder_for of { a : Str }(tag Default, param value, lit) ; lambda -> Test.encode(param r) | Test.encode_str = lambda -> tag Ok ; Token.encoder_for = lambda -> Test.encode_str(other, param state) ; Test.encode#1 = lambda -> Token.encoder_for(tag Default, param value, lit) ; lambda -> Test.encode#1(param t)\"" },
    },
    .{
        .name = "staging - every spelling of inversion describes as one Unary",
        .source_kind = .module,
        .source = staged_not_spellings,
        .expected = .{ .inspect_str = "\"not not not\"" },
    },
    .{
        .name = "staging - a Code parameter handed on is not staged again",
        .source_kind = .module,
        .source = staged_record_field,
        .expected = .{ .inspect_str = "\"lambda -> (param p.x plus param p.y)\"" },
    },
    .{
        .name = "staging - every field of a record parameter reaches the stage",
        .source_kind = .module,
        .source = staged_record_parameter,
        .expected = .{ .inspect_str = "\"3 of 3\"" },
    },
    .{
        .name = "staging - a tag union parameter names its variants and their payloads",
        .source_kind = .module,
        .source = staged_tag_union_type,
        .expected = .{ .inspect_str = "\"[Blue/0, Green/2, Red/0]\"" },
    },
    .{
        .name = "staging - a recursive nominal names itself inside its own backing",
        .source_kind = .module,
        .source = staged_recursive_type,
        .expected = .{ .inspect_str = "\"Tree = [Leaf(), Node(^Tree, ^Tree)]\"" },
    },
    .{
        .name = "staging - a recursive nominal with a type parameter names itself inside its own backing",
        .source_kind = .module,
        .source = staged_recursive_parametric_type,
        .expected = .{ .inspect_str = "\"Tree = [Leaf(), Node(^Tree, U16)]\"" },
    },
    .{
        .name = "staging - a recursive nominal that changes its type argument takes a Named per instantiation",
        .source_kind = .module,
        .source = staged_recursive_changing_argument,
        .expected = .{ .inspect_str = "\"Chain = [End(), Link(F32, Chain = [End(), Link(U16, ^Chain)])]\"" },
    },
    .{
        .name = "staging - children hands back every sub-expression, guards and loop parts among them",
        .source_kind = .module,
        .source = staged_ir_children,
        .expected = .{ .inspect_str = "\"31 nodes, Builtin.Num.U16.min Builtin.Num.F32.min Builtin.Num.U16.to_f32\"" },
    },
    .{
        .name = "staging - numeric answers what a number is and name spells any type",
        .source_kind = .module,
        .source = staged_ty_questions,
        .expected = .{ .inspect_str = "\"F32 frac 32 signed | U16 int 16 unsigned | Dec fixed 128 signed | Point not numeric | List(Str) not numeric | [Green(U8), Red] not numeric\"" },
    },
    .{
        .name = "staging - a match describes its subject, patterns, guards and branch values",
        .source_kind = .module,
        .source = staged_match,
        .expected = .{ .inspect_str = "\"match c { Red() | Blue() => 1 Green(v) if (v is_gt 0) => v Green(_) => 0 }\"" },
    },
    .{
        .name = "staging - a literal, a wildcard and a binder inside a record pattern",
        .source_kind = .module,
        .source = staged_match_patterns,
        .expected = .{ .inspect_str = "\"match r { {a: 0 b: b} => b {a: a b: _} => a }\"" },
    },
    .{
        .name = "staging - constructing a tag describes as MakeTag",
        .source_kind = .module,
        .source = staged_make_tag,
        .expected = .{ .inspect_str = "\"Green(x)\"" },
    },
    .{
        .name = "staging - a recursive nominal is built and matched in a staged body",
        .source_kind = .module,
        .source = staged_recursive_value,
        .expected = .{ .inspect_str = "\"match t { Leaf() => Node(Leaf() Leaf()) Node(l _r) => Node(l t) }\"" },
    },
    .{
        .name = "staging - and describes as the if it short-circuits through",
        .source_kind = .module,
        .source = staged_and,
        .expected = .{ .inspect_str = "\"if (x is_gt 1) then (x is_lt 2) else False\"" },
    },
    .{
        .name = "staging - a plain call to a named function is described by name",
        .source_kind = .module,
        .source = staged_plain_call,
        .expected = .{ .inspect_str = "\"lambda -> (Test.step(param x) plus Test.step(Test.step(param x)))\"" },
    },
    .{
        .name = "staging - a recursive call describes, because the callee is named rather than inlined",
        .source_kind = .module,
        .source = staged_recursive_call,
        .expected = .{ .inspect_str = "\"lambda -> if (param x is_gt 0) then Test.countdown((param x minus 1)) else 0\"" },
    },
    .{
        .name = "staging - a callee's description arrives beside the root, once however many calls reach it",
        .source_kind = .module,
        .source = staged_call_table,
        .expected = .{ .inspect_str = "\"Test.step = lambda -> (param x plus 1) || lambda -> (Test.step(param x) plus Test.step(Test.step(param x)))\"" },
    },
    .{
        .name = "staging - a callee comes before its caller in the table",
        .source_kind = .module,
        .source = staged_call_chain,
        .expected = .{ .inspect_str = "\"Test.inner = lambda -> (param x plus 1) ; Test.middle = lambda -> (Test.inner(param x) times 2) || lambda -> (Test.middle(param x) minus Test.inner(param x))\"" },
    },
    .{
        .name = "staging - two sites reaching one callee each carry a row for it",
        .source_kind = .module,
        .source = staged_call_shared,
        .expected = .{ .inspect_str = "\"Test.step = lambda -> (param x plus 1) || lambda -> Test.step(param x) | Test.step = lambda -> (param x plus 1) || lambda -> Test.step(Test.step(param x))\"" },
    },
    .{
        .name = "staging - a recursive function is a row of its own table",
        .source_kind = .module,
        .source = staged_recursive_table,
        .expected = .{ .inspect_str = "\"Test.countdown = lambda -> if (param x is_gt 0) then Test.countdown((param x minus 1)) else 0 || lambda -> if (param x is_gt 0) then Test.countdown((param x minus 1)) else 0\"" },
    },
    .{
        .name = "staging - a derived == over a tag union describes as the match it is",
        .source_kind = .module,
        .source = staged_derived_eq,
        .expected = .{ .inspect_str = "\"match (a b) { (Green(eq_lhs_0) Green(eq_rhs_0)) => (eq_lhs_0 is_eq eq_rhs_0) (Red() Red()) => True _ => False }\"" },
    },
    .{
        .name = "staging - a derived == over a nominal names the nominal in its patterns",
        .source_kind = .module,
        .source = staged_derived_eq_nominal,
        .expected = .{ .inspect_str = "\"(Color Color) (Color Color) (Color Color)\"" },
    },
    .{
        .name = "staging - a row the checker closed describes, so List.get describes",
        .source_kind = .module,
        .source = staged_list_index,
        .expected = .{ .inspect_str = "\"Builtin.List.get : Builtin.Try(U64, [OutOfBounds])\"" },
    },
    .{
        .name = "staging - a template's compile-time argument is folded into the description",
        .source_kind = .module,
        .source = staged_template,
        .expected = .{ .inspect_str = "\"lambda -> (param x times 3)\"" },
    },
    .{
        .name = "staging - two calls of one template describe two bodies",
        .source_kind = .module,
        .source = staged_template_twice,
        .expected = .{ .inspect_str = "\"lambda -> (param x times 2) | lambda -> (param x times 7)\"" },
    },
    .{
        .name = "staging - a template takes a list, and a staged body writes one",
        .source_kind = .module,
        .source = staged_list,
        .expected = .{ .inspect_str = "\"lambda -> (param x times Builtin.Num.U64.to_f32(Builtin.List.len([2, 4])))\"" },
    },
    .{
        .name = "staging - a template takes a record, and a field of it is read from the description",
        .source_kind = .module,
        .source = staged_record_argument,
        .expected = .{ .inspect_str = "\"lambda -> (param x times {dx: 3, dy: 0.5}.dx)\"" },
    },
    .{
        .name = "staging - a template folds every argument it names",
        .source_kind = .module,
        .source = staged_template_many,
        .expected = .{ .inspect_str = "\"lambda -> ((param x times 2) plus 5)\"" },
    },
    .{
        .name = "staging - a reified function hands back a nullary tag",
        .source_kind = .module,
        .source = staged_nullary_tag_result,
        .expected = .{ .inspect_str = "\"lambda\"" },
    },
    .{
        .name = "staging - an empty list and an empty record describe as the aggregates they are",
        .source_kind = .module,
        .source = staged_empty_aggregate,
        .expected = .{ .inspect_str = "\"list of 0 ; record of 0\"" },
    },
    .{
        .name = "staging - a top-level value read from a staged body is the value it holds",
        .source_kind = .module,
        .source = staged_top_level_constant,
        .expected = .{ .inspect_str = "\"lambda -> (param x times 2)\"" },
    },
    .{
        .name = "staging - a value another module exports folds the same way",
        .source_kind = .module,
        .source = staged_imported_constant,
        .imports = &.{.{
            .name = "Limits",
            .source =
            \\Limits :: {}.{
            \\    ceiling : F32
            \\    ceiling = 7.0.F32
            \\}
            ,
        }},
        .expected = .{ .inspect_str = "\"lambda -> (param x times 7)\"" },
    },
    .{
        .name = "staging - a top-level record folds whole, and a field read reaches into it",
        .source_kind = .module,
        .source = staged_constant_record,
        .expected = .{ .inspect_str = "\"lambda -> (param x times {gain: 3, bias: 0.5}.gain)\"" },
    },
    .{
        .name = "staging - a name as a template argument folds to the value it holds",
        .source_kind = .module,
        .source = staged_constant_template_argument,
        .expected = .{ .inspect_str = "\"lambda -> (param x times 4)\"" },
    },
    .{
        .name = "staging - a default operand binds a name the walk invented",
        .source_kind = .module,
        .source = staged_default_operand,
        .expected = .{ .inspect_str = "\"match t { Ok(bind#0) => bind#0 Err(_) => fallback }\"" },
    },
    .{
        .name = "staging - an as pattern keeps its name beside the pattern it renames",
        .source_kind = .module,
        .source = staged_as_pattern,
        .expected = .{ .inspect_str = "\"match p { {a: _ b: _} as whole => whole.a }\"" },
    },
    .{
        .name = "staging - a numeral of the author's own type names the conversion that makes it",
        .source_kind = .module,
        .source = staged_custom_numeral,
        .expected = .{ .inspect_str = "\"lambda -> Meters.scale(Meters.from_numeral(3) param x)\"" },
    },
    .{
        .name = "staging - a quoted literal of the author's own type names its conversion",
        .source_kind = .module,
        .source = staged_custom_quote,
        .expected = .{ .inspect_str = "\"lambda -> Name.width(Name.from_quote(hi) param x)\"" },
    },
    .{
        .name = "staging - each alternative of a literal pattern carries its own condition",
        .source_kind = .module,
        .source = staged_custom_literal_pattern,
        .expected = .{ .inspect_str = "\"match c { bind#0 when (bind#0 is_eq Count.from_numeral(7)) | bind#1 when (bind#1 is_eq Count.from_numeral(8)) => f _ => 0 }\"" },
    },
    .{
        .name = "staging - a plain call to a builtin takes the name a method call on it takes",
        .source_kind = .module,
        .source = staged_builtin_call,
        .expected = .{ .inspect_str = "\"lambda -> if Builtin.Str.is_empty(Builtin.Num.F32.to_str(param x)) then param x else param x | lambda -> if Builtin.Str.is_empty(Builtin.Num.F32.to_str(param x)) then param x else param x\"" },
    },
    .{
        .name = "staging - a builtin is named, and no row is written for it",
        .source_kind = .module,
        .source = staged_builtin_call_table,
        .expected = .{ .inspect_str = "\" || lambda -> if Builtin.Str.is_empty(Builtin.Num.F32.to_str(param x)) then param x else param x\"" },
    },
    .{
        .name = "staging - an interpolated literal describes as the concatenation it is",
        .source_kind = .module,
        .source = staged_interpolation,
        .expected = .{ .inspect_str = "\"lambda -> if Builtin.Str.is_empty(let bind#0 = Builtin.Num.F32.to_str(param x) in Builtin.Str.concat(Builtin.Str.concat(p local bind#0) q)) then param x else param x | lambda -> if Builtin.Str.is_empty(let bind#1 = Builtin.Num.F32.to_str(param x) in local bind#1) then param x else param x\"" },
    },
    .{
        .name = "staging - a top-level value folds at the wider union its use reads",
        .source_kind = .module,
        .source = staged_widened_value,
        .expected = .{ .inspect_str = "\"match Fast : [Fast Slow] { x other }\"" },
    },
    .{
        .name = "staging - a call result of the union its callee's body closed reaches a wider match as it is",
        .source_kind = .module,
        .source = staged_widened_call,
        .expected = .{ .inspect_str = "\"match other { x other other }\"" },
    },
    .{
        .name = "staging - an interpolated literal of the author's own type is refused",
        .source_kind = .module,
        .source = staged_custom_interpolation,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a record update describes as the record it builds",
        .source_kind = .module,
        .source = staged_record_update,
        .expected = .{ .inspect_str = "\"lambda -> let base = {x: param v, y: 1} in let moved = {y: 2, x: local base.x} in (local moved.x plus local moved.y)\"" },
    },
    .{
        .name = "staging - a record update binds a subject that is not a name",
        .source_kind = .module,
        .source = staged_record_update_binds,
        .expected = .{ .inspect_str = "\"lambda -> let moved = let bind#0 = {x: param v, y: 1} in {y: 2, x: local bind#0.x} in (local moved.x plus local moved.y)\"" },
    },
    .{
        .name = "staging - an unset field is left out, and the type says it may be absent",
        .source_kind = .module,
        .source = staged_unset_field,
        .expected = .{ .inspect_str = "\"lambda -> let c = {a: v} : {a b?} in c.a\"" },
    },
    .{
        .name = "staging - a read of an optional field carries the Try it hands back",
        .source_kind = .module,
        .source = staged_optional_field,
        .expected = .{ .inspect_str = "\"lambda -> let c = {a: v} : {b? a} in match c.?b : Builtin.Try(F32 [MissingField]) { f v }\"" },
    },
    .{
        .name = "staging - a record pattern drops a rest that binds nothing",
        .source_kind = .module,
        .source = staged_record_rest,
        .expected = .{ .inspect_str = "\"match p { {x: x} => x }\"" },
    },
    .{
        .name = "staging - a list pattern with a rest is a node of its own",
        .source_kind = .module,
        .source = staged_list_pattern,
        .expected = .{ .inspect_str = "\"match l { [a b] => (a minus b) [a .. b] => (a plus b) [a ..mid b] => (a times b) _ => 0 }\"" },
    },
    .{
        .name = "staging - a string pattern is transcribed step by step",
        .source_kind = .module,
        .source = staged_str_pattern,
        .expected = .{ .inspect_str = "\"match s { 'a'..head'b'..''.. => head ''..tail'z' => tail _ => s }\"" },
    },
};
