//! Staging: a Roc function named where a `Code` is expected becomes a
//! description, and a stage written in Roc reads it while the compiler runs.
//!
//! Every case here goes the whole way through `roc build`: the checker records
//! the site, publication walks the named function into the module's const
//! store, lowering restores the stored description at the site, and the stage
//! turns it into the value `main` inspects.

const TestCase = @import("parallel_runner.zig").TestCase;

/// A stage that prints every row of a description through `Graph.to_tree`.
/// Shared by the cases below so each one differs only in the function it stages.
const stage =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| {
    \\        graph = Code.graph(code)
    \\        first = graph.root_row()
    \\        others = graph.rows().keep_if(|other| other.id != first.id)
    \\        shown = [first].concat(others).map(|each| "r${each.id.to_str()} = ${Stage.row(graph, each)}")
    \\        Str.join_with(shown, " ; ")
    \\    }
    \\
    \\    row : Code.Graph, Code.Row -> Str
    \\    row = |graph, described| {
    \\        params = Str.join_with(described.params.map(|param| param.name()), ", ")
    \\        "|${params}| -> ${described.result.name()} ${Stage.tree(graph.to_tree(described.id))}"
    \\    }
    \\
    \\    tree : Code.Tree -> Str
    \\    tree = |t| match t {
    \\        Op(o) => Stage.op(o.op, o.args)
    \\        Param(k) => "p${k.to_str()}"
    \\        Input(k) => "in${k.to_str()}"
    \\        Arg(a) => "s${a.owner.to_str()}.${a.k.to_str()}"
    \\        Out(o) => "n${o.node.to_str()}.${o.k.to_str()}"
    \\        Def(n) => "n${n.to_str()}"
    \\        Block(b) => {
    \\            defs = b.defs.map(|d| "n${d.id.to_str()} = ${Stage.tree(d.value)}; ")
    \\            last = match b.end {
    \\                Value(vals) => Stage.all(vals)
    \\                Jump(j) => "jump j${j.join.to_str()}(${Stage.all(j.args)})"
    \\                Return(v) => "return ${Stage.tree(v)}"
    \\                Continue(vals) => "continue(${Stage.all(vals)})"
    \\                Break(vals) => "break(${Stage.all(vals)})"
    \\                Branch(sw) => Stage.tree(sw)
    \\            }
    \\            if defs.is_empty() last else "{ ${Str.join_with(defs, "")}${last} }"
    \\        }
    \\    }
    \\
    \\    all : List(Code.Tree) -> Str
    \\    all = |ts| Str.join_with(ts.map(Stage.tree), ", ")
    \\
    \\    op : Code.Op, List(Code.Tree) -> Str
    \\    op = |o, args| match o {
    \\        Lit(l) => Stage.lit(l)
    \\        Prim(p) => "${p.owner}.${p.method}(${Stage.all(args)})"
    \\        Call(r) => "r${r.to_str()}(${Stage.all(args)})"
    \\        Closure(r) => "closure r${r.to_str()}(${Stage.all(args)})"
    \\        Record(names) => {
    \\            fields = List.map2(names, args, |name, arg| "${name}: ${Stage.tree(arg)}")
    \\            if fields.is_empty() "{}" else "{ ${Str.join_with(fields, ", ")} }"
    \\        }
    \\        Tuple => "(${Stage.all(args)})"
    \\        List => "[${Stage.all(args)}]"
    \\        Tag(name) => "${name}(${Stage.all(args)})"
    \\        Wrap(name) => "${name}.(${Stage.all(args)})"
    \\        Unwrap => "unwrap(${Stage.all(args)})"
    \\        Field(name) => "${Stage.all(args)}.${name}"
    \\        Index(i) => "${Stage.all(args)}.${i.to_str()}"
    \\        Payload(name, i) => "${Stage.all(args)}.${name}.${i.to_str()}"
    \\        Item => "item(${Stage.all(args)})"
    \\        OptField(name) => "${Stage.all(args)}.?${name}"
    \\        Switch(sw) => {
    \\            scrutinee = Stage.all(args.take_first(1))
    \\            arms = List.map2(sw.arms, args.drop_first(1), |arm, body| "${Stage.key(arm.key)} => ${Stage.tree(body)}")
    \\            joins = args.drop_first(1 + sw.arms.len()).map_with_index(|body, i| " j${i.to_str()}: ${Stage.tree(body)}")
    \\            "switch ${scrutinee} { ${Str.join_with(arms, " | ")} }${Str.join_with(joins, "")}"
    \\        }
    \\        And(_) => "and(${Stage.all(args)})"
    \\        Or(_) => "or(${Stage.all(args)})"
    \\        ForRange(r) => "for_range${if r.inclusive "=" else "<"}(${Stage.all(args)})"
    \\        ForList(_) => "for_list(${Stage.all(args)})"
    \\        Loop(_) => "loop(${Stage.all(args)})"
    \\        Lambda(_) => "lambda(${Stage.all(args)})"
    \\        Crash => "crash(${Stage.all(args)})"
    \\        Derived(name, _) => "derived ${name}(${Stage.all(args)})"
    \\    }
    \\
    \\    lit : Code.Lit -> Str
    \\    lit = |value| match value {
    \\        Bool(flag) => if flag "True" else "False"
    \\        Int(number, _) => number.to_str()
    \\        Frac(number, _) => number.to_str()
    \\        Fixed(number) => number.to_str()
    \\        Str(text) => "'${text}'"
    \\        Bytes(bytes) => "bytes[${Str.join_with(bytes.map(|b| b.to_str()), " ")}]"
    \\    }
    \\
    \\    key : Code.Key -> Str
    \\    key = |k| match k {
    \\        Tag(name) => name
    \\        Lit(l) => Stage.lit(l)
    \\        Len(n) => "len ${n.to_str()}"
    \\        AtLeast(n) => "len >= ${n.to_str()}"
    \\        Default => "_"
    \\    }
    \\
    \\    root : Code(f) -> Str
    \\    root = |code| {
    \\        graph = Code.graph(code)
    \\        Stage.tree(graph.to_tree(graph.root_row().id))
    \\    }
    \\}
    \\
;

const staged_binop = stage ++
    \\double : F32 -> F32
    \\double = |x| x * 2.0.F32
    \\main = Stage.describe(double)
;

// A binding the body reads twice is one node that both reads share. That is
// the property a shader stage needs: one Roc binding becomes one GLSL local,
// used twice.
const staged_let = stage ++
    \\wobble : F32 -> F32
    \\wobble = |x| {
    \\    wave = x * 2.0.F32
    \\    wave + wave
    \\}
    \\main = Stage.describe(wobble)
;

// A lambda the staged function returns is lifted into a row of its own, and
// the name it reads from the lambda around it is a capture the `Closure` passes
// as its row's leading parameter.
const staged_nested_lambda = stage ++
    \\adder : F32 -> (F32 -> F32)
    \\adder = |a| |b| a + b
    \\main = Stage.describe(adder)
;

// `!b`, `Bool.not(b)` and `b.not()` are one operation, so all three describe
// as the one `Bool.not` primitive a translator already handles.
const staged_not_spellings = stage ++
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

// A generic callee is one row per instantiation: the body is one, and what it
// reads at is not, so a translator emits one function per type it is used at.
// Each instantiation is called twice, so the graph view keeps it a row (V1).
const staged_generic_instantiations = stage ++
    \\wrap : a -> List(a)
    \\wrap = |p| [p]
    \\
    \\mix : F32 -> U64
    \\mix = |x| wrap(x).len() + wrap(x + 1.0.F32).len() + wrap("s").len() + wrap("t").len()
    \\main = Stage.describe(mix)
;

// A generic callee that calls a generic function writes the inner call in its
// own variables, so the inner row is keyed by what the outer call fixed them
// to rather than by a type that still holds a variable. Each callee is called
// twice, so the graph view keeps it a row (V1).
const staged_generic_nested = stage ++
    \\single : a -> List(a)
    \\single = |v| [v]
    \\
    \\both : b, b -> List(b)
    \\both = |v, w| single(v).concat(single(w))
    \\
    \\mix : F32 -> U64
    \\mix = |x| both(x, x + 1.0.F32).len() + both(x + 2.0.F32, x).len()
    \\main = Stage.describe(mix)
;

// A variable the scheme reaches only through a record is fixed by the record
// the call passes, so the row reads its field at the type the call fixed.
//
// The calls pass records of one checked type id, which is why the `Ty`
// cache has to refuse a subtree a substitution answered inside: caching it
// would hand the second instantiation the first one's field type. Each
// instantiation is called twice, so the graph view keeps it a row (V1).
const staged_generic_record = stage ++
    \\field : { v : a } -> a
    \\field = |r| r.v
    \\
    \\mix : F32 -> Str
    \\mix = |x| field({ v: x }).to_str().concat(field({ v: "s" })).concat(field({ v: x + 1.0.F32 }).to_str()).concat(field({ v: "t" }))
    \\main = Stage.describe(mix)
;

// A `where`-constrained callee dispatches on its own quantified variable, so
// the substitution is what turns `to_str` into a call named by the type the
// call fixed it to. Each callee has one call, so the graph view inlines it
// (V1), and the name is the one the site reads.
const staged_generic_where = stage ++
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

// A lambda written in a generic callee is part of that callee, so it
// describes under the instantiation the call fixed: one row per type, a
// nested lambda and one that captures a parameter of the callee included.
const staged_generic_lambdas = stage ++
    \\firsts : List((a, b)) -> List(a)
    \\firsts = |xs| xs.map(|p| p.0)
    \\
    \\pairs : List(a), b -> List((a, b))
    \\pairs = |xs, k| xs.map(|x| (x, k))
    \\
    \\nested : List(List(a)) -> List(List((a, a)))
    \\nested = |xss| xss.map(|xs| xs.map(|x| (x, x)))
    \\
    \\mix : List(F32), List(Str) -> U64
    \\mix = |a, b| firsts(pairs(a, "k")).len() + firsts(pairs(b, 1.0.F32)).len() + nested([a]).len()
    \\main = Stage.describe(mix)
;

// A lambda in a generic callee dispatches through the evidence the call
// supplied, and a `where` obligation's own open row is a row of the scheme,
// which no call fixes. A lambda the callee's block generalized is fixed by
// its lookup on top of what the call fixed.
const staged_generic_lambda_where = stage ++
    \\bump : List(a) -> List(a) where [a.plus : a, a -> a, a.from_numeral : Numeral -> Try(a, [InvalidNumeral(Str)])]
    \\bump = |xs| xs.map(|x| x + 1)
    \\
    \\dup : List(a) -> List((a, a))
    \\dup = |xs| {
    \\    pair = |x| (x, x)
    \\    xs.map(|x| pair(x))
    \\}
    \\
    \\go : List(U16) -> U64
    \\go = |xs| bump(xs).len() + dup(xs).len()
    \\main = Stage.describe(go)
;

// An arithmetic parameter no literal pins takes the numeric default, `Dec`,
// as it would in a compiled function. A site inside a function body takes it
// at that function's boundary.
const staged_numeric_default = stage ++
    \\label : U8 -> Str
    \\label = |_n| Stage.describe(|x| x - 1)
    \\main = "${Stage.describe(|x| x * 2)} | ${Stage.describe(|x, y| x + y)} | ${label(3)}"
;

// The literal of an unannotated helper has a type variable that only its
// `times` obligation names. The checker's record of each use fixes it: `Dec`
// at the site, `U8` at the call.
const staged_unannotated_literal = stage ++
    \\triple = |x| x * 3
    \\small : U8 -> U8
    \\small = |y| triple(y)
    \\main = "${Stage.describe(triple)} | ${Stage.describe(small)}"
;

// A lambda written at the site is described rather than lowered, and the
// calls it makes still read what each use fixed its callee to: the literal of
// `helper`, the element type of `bump`, and the local `g` its block
// generalized all take `U64` from the call.
const staged_inline_unannotated_calls = stage ++
    \\helper = |x| x + 1
    \\bump = |xs| xs.map(|x| x + 1)
    \\local = Stage.describe(|s| {
    \\    g = |y| y + 1
    \\    g(g(Str.count_utf8_bytes(s)))
    \\})
    \\main = "${Stage.describe(|s| helper(Str.count_utf8_bytes(s)))} | ${Stage.describe(|s| bump([Str.count_utf8_bytes(s)]))} | ${local}"
;

// An unannotated helper that calls another hands it what its own caller
// discharged its `where` obligations with: `outer2` forwards `inc`'s `plus`
// to its own, which the site discharges at `U64`, and `outer` forwards
// `inner`'s `times` the same way. `top` forwards through two helpers.
const staged_generic_calls_generic = stage ++
    \\inc = |x| x + 1
    \\outer2 = |x| inc(x)
    \\top = |x| outer2(x)
    \\inner = |xs| xs.map(|x| x * 2)
    \\outer = |xs| inner(xs)
    \\outermost = |xs| outer(xs)
    \\named = |s| outer([Str.count_utf8_bytes(s)])
    \\main = "${Stage.describe(|s| outer2(Str.count_utf8_bytes(s)))} | ${Stage.describe(|s| outer([Str.count_utf8_bytes(s)]))} | ${Stage.describe(named)} | ${Stage.describe(|s| top(Str.count_utf8_bytes(s)))} | ${Stage.describe(|s| outermost([Str.count_utf8_bytes(s)]))}"
;

// A function parameter the call fixed stays that definition inside a lambda
// that captures it, so the lambda a builtin receives names it.
const staged_bound_capture = stage ++
    \\apply_all = |xs, f| xs.map(|x| f(x))
    \\each = |xs, f| xs.map(f)
    \\twice = |xs, f| xs.map(|x| f(f(x)))
    \\go : List(I64) -> (List(I64), List(I64), List(I64))
    \\go = |xs| (apply_all(xs, |x| x * 3), each(xs, |x| x + 1), twice(xs, |x| x - 1))
    \\main = Stage.describe(go)
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
// instantiated it names the target. Each row has one call, so the graph view
// inlines it (V1), and the site reads the method's body.
const staged_type_dispatch = stage ++
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
// name with nothing behind it. The method is called twice, so the graph view
// keeps it a row (V1).
const staged_method_definition = stage ++
    \\Token := { raw : Str }.{
    \\    label : Token -> Str
    \\    label = |t| t.raw
    \\}
    \\
    \\name : Token, Token -> Str
    \\name = |t, u| t.label().concat(u.label())
    \\main = Stage.describe(name)
;

// A parametric nominal's backing is the declaration's template, written in the
// nominal's own variables, and what a use fixes them to is on the use. Reading
// the two together is what makes `Box(F32)` a `Box` of `F32`, and it is what a
// derived `map` needed: the mapping function is a `Closure` of a row of its own,
// and the subject is the nominal the compiler derived against.
const staged_parametric_nominal = stage ++
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
// set of callees, the way a generic definition takes one per instantiation,
// and a row that only calls its function argument is that call (N8c). A
// lambda written at the call site is lifted into a row of its own. Each row
// is called twice, so the graph view keeps it (V1).
const staged_function_argument = stage ++
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
    \\named = |x| apply_to(double, x) + apply_to(triple, x) + apply_to(double, x + 1.0.F32) + apply_to(triple, x + 1.0.F32)
    \\
    \\written : F32 -> F32
    \\written = |x| apply_to(|y| y - 1.0.F32, x) * apply_to(|y| y - 1.0.F32, x + 2.0.F32)
    \\main = "${Stage.describe(named)} | ${Stage.describe(written)}"
;

// A lambda a block bound is a row of its own, so the binding leaves no node
// behind and the call names the row. The row is described with none of the
// scope around it, so what the lambda captured arrives as a parameter, which
// takes its place in the row's first-read order (N8f). Each lambda is called
// twice, so the graph view keeps it a row (V1).
const staged_local_lambda = stage ++
    \\plain : F32 -> F32
    \\plain = |x| {
    \\    step : F32 -> F32
    \\    step = |y| y * 2.0.F32
    \\    step(x) + step(x + 1.0.F32)
    \\}
    \\
    \\capturing : F32 -> F32
    \\capturing = |x| {
    \\    step : F32 -> F32
    \\    step = |y| y * x
    \\    step(1.0.F32) + step(2.0.F32)
    \\}
    \\main = "${Stage.describe(plain)} | ${Stage.describe(capturing)}"
;

// A definition that hands back a function and the call that runs it are one
// row and one `Call`: the row gathers both lambdas' parameters, and the call
// passes the constructor's arguments and the applied ones, in the row's
// first-read order (N8f). Bound first and run later is the same thing held in
// scope. Each row is called twice, so the graph view keeps it (V1).
const staged_curried_call = stage ++
    \\scaler : F32 -> (F32 -> F32)
    \\scaler = |k| |x| x * k
    \\
    \\direct : F32 -> F32
    \\direct = |x| scaler(2.0.F32)(x) + scaler(3.0.F32)(x)
    \\
    \\held : F32 -> F32
    \\held = |x| {
    \\    twice = scaler(2.0.F32)
    \\    twice(x) + twice(x + 1.0.F32)
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

// A derived codec is curried: the body constructs the encoder and then runs
// it. Applying a function value has no node, so the two halves describe as one
// `Derived` the stage expands, with the constructor's arguments before the
// applied ones. `encode` has one call, so the graph view inlines it (V1).
const staged_derived_codec = stage ++ codec_format ++
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
// that can tell the two apart. Each row with one call is inlined (V1); the
// closure the author wrote stays a row, because a `Closure` names it.
const staged_codec_origin = stage ++ codec_format ++
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
// one describes as its body, where a derived one describes as the `Derived` a
// stage expands. Both read the same arguments, which is what lets one
// translator read either. Each row has one call, so the graph view inlines it
// (V1); the state is a parameter, so no literal folds it away.
const staged_codec_applied = stage ++ codec_format ++
    \\Token := { raw : Str }.{
    \\    encoder_for : Format -> (Token, U64 -> Try(U64, []))
    \\    encoder_for = |_f| |token, state| Format.encode_str(token.raw, state)
    \\}
    \\
    \\encode : value, U64 -> Try(U64, [])
    \\    where [
    \\        value.encoder_for : Format -> (value, U64 -> Try(U64, [])),
    \\    ]
    \\encode = |value, state| {
    \\    Shape : value
    \\    Shape.encoder_for(Format.Default)(value, state)
    \\}
    \\
    \\by_shape : { a : Str }, U64 -> Try(U64, [])
    \\by_shape = |r, state| encode(r, state)
    \\
    \\by_hand : Token, U64 -> Try(U64, [])
    \\by_hand = |t, state| encode(t, state)
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
    \\    describe = |code| Stage.describe(code)
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
    \\    fields = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.labels(p)), " | ")
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
    \\    variants = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.ty(p)), " | ")
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
    \\    param = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.ty(p)), " | ")
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
    \\    param = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.ty(p)), " | ")
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
    \\    param = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.ty(p)), " | ")
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

// `Node.children` hands back a node's arguments and the regions it owns,
// whatever kind it is, so a pass with nothing to say about kinds walks with it
// instead of writing an arm per kind. A guard's test is in an arm of its
// `Switch`, and a loop's body is the region of its `ForList`.
const staged_ir_children =
    \\Shape :: {}.{
    \\    walk : Code(f) -> Str
    \\    walk = |code| {
    \\        row = Code.graph(code).root_row()
    \\        "${Shape.count(row, row.body).to_str()} nodes, ${Str.join_with(Shape.prims(row, row.body), " ")}"
    \\    }
    \\
    \\    count : Code.Row, Code.Region -> U64
    \\    count = |row, region| region.nodes.map(|n| 1 + row.node(n).children().regions.map(|r| Shape.count(row, r)).sum()).sum()
    \\
    \\    prims : Code.Row, Code.Region -> List(Str)
    \\    prims = |row, region| region.nodes.join_map(|n| {
    \\        node = row.node(n)
    \\        here = match node.op {
    \\            Prim(p) => ["${p.owner}.${p.method}"]
    \\            _ => []
    \\        }
    \\        List.concat(here, node.children().regions.join_map(|r| Shape.prims(row, r)))
    \\    })
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
    \\    ask = |code| Str.join_with(Code.graph(code).root_row().params.map(|p| Shape.about(p)), " | ")
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

// A `match` over a tag union, with everything a branch can carry: an
// alternative, a guard, a payload read in the branch value, and a wildcard
// payload. It describes as a `Switch` on the tag, and the guard as a `Switch`
// on a `Bool` inside the arm.
const staged_match = stage ++
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

// A literal pattern and a wildcard inside a record pattern, with a binder
// beside them: the literal is a `Switch` on the field it tests.
const staged_match_patterns = stage ++
    \\pick : { a : U8, b : U8 } -> U8
    \\pick = |r| match r {
    \\    { a: 0, b } => b
    \\    { a, b: _ } => a
    \\}
    \\main = Stage.describe(pick)
;

// Constructing a tag, and a Bool, which is the one tag union with a literal.
const staged_make_tag = stage ++
    \\Color := [Red, Green(F32), Blue]
    \\
    \\paint : F32 -> Color
    \\paint = |x| Color.Green(x)
    \\main = Stage.describe(paint)
;

// A recursive nominal is a value like any other once its type describes: the
// body builds one and matches one, and the payload the match binds is itself
// a `Tree`.
const staged_recursive_value = stage ++
    \\Tree := [Leaf, Node(Tree, Tree)]
    \\
    \\grow : Tree -> Tree
    \\grow = |t| match t {
    \\    Leaf => Tree.Node(Tree.Leaf, Tree.Leaf)
    \\    Node(l, _r) => Tree.Node(l, t)
    \\}
    \\main = Stage.describe(grow)
;

// `and` describes as one `And` node, whose later operand is a region that
// runs only where the first operand holds.
const staged_and = stage ++
    \\band : F32 -> Bool
    \\band = |x| x > 1.0 and x < 2.0
    \\main = Stage.describe(band)
;

// A function that returns a `Code` is a template: the compiler calls it and
// writes the arguments into the description, so the parameter the template
// took is a literal by the time the stage reads the body.
const staged_template = stage ++
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |factor| |x| x * factor
    \\main = Stage.describe(scaled(3.0.F32))
;

// One template, two calls, two descriptions. This is what makes a template
// worth having: the threshold is in the description rather than in the source.
const staged_template_twice = stage ++
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |factor| |x| x * factor
    \\main = "${Stage.describe(scaled(2.0.F32))} | ${Stage.describe(scaled(7.0.F32))}"
;

// A template takes as many compile-time arguments as it likes, and one it never
// names is simply absent from the description.
const staged_template_many = stage ++
    \\shifted : F32, Str, F32 -> Code(F32 -> F32)
    \\shifted = |factor, _label, offset| |x| x * factor + offset
    \\main = Stage.describe(shifted(2.0.F32, "unused", 5.0.F32))
;

// A list a staged body writes is a `List` node, which is also what lets a
// template take one: a compile-time argument is written into the description,
// so every part of it has to be something the normal form can hold.
const staged_list = stage ++
    \\scaled : List(F32) -> Code(F32 -> F32)
    \\scaled = |steps| |x| x * steps.len().to_f32()
    \\main = Stage.describe(scaled([2.0.F32, 4.0.F32]))
;

// A record argument arrives whole, and a field read of it folds to the field
// the call fixed.
const staged_record_argument = stage ++
    \\shifted : { dx : F32, dy : F32 } -> Code(F32 -> F32)
    \\shifted = |by| |x| x * by.dx
    \\main = Stage.describe(shifted({ dx: 3.0.F32, dy: 0.5.F32 }))
;

// A plain call to a definition of this module is a `Call` of the callee's
// row, and the callee's body is that row, not written into the caller.
const staged_plain_call = stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x) + step(step(x))
    \\main = Stage.describe(bump)
;

/// A stage that names its site at `Code(F32 -> F32)`, for the cases that stage
/// a function by name there. It prints every row, so what a `Call` reaches is
/// visible rather than only the row id.
const table_stage = stage ++
    \\Table :: {}.{
    \\    describe : Code(F32 -> F32) -> Str
    \\    describe = |code| Stage.describe(code)
    \\}
    \\
;

// The callee's row arrives beside the root, so a translator emits one
// function per row. `step` is called three times and described once.
const staged_call_table = table_stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x) + step(step(x))
    \\main = Table.describe(bump)
;

// Rows come in the order the walk reaches them: a callee's row follows the
// row that first calls it. Each callee is called twice with two arguments,
// so the graph view keeps it a row (V1).
const staged_call_chain = table_stage ++
    \\inner : F32 -> F32
    \\inner = |x| x + 1.0
    \\middle : F32 -> F32
    \\middle = |x| inner(x) * 2.0
    \\outer : F32 -> F32
    \\outer = |x| middle(x) - middle(inner(x * 3.0))
    \\main = Table.describe(outer)
;

// Two sites reaching one callee each get a row for it, and the walk describes
// that callee once. Each site calls it twice, so the graph view keeps it a
// row (V1).
const staged_call_shared = table_stage ++
    \\step : F32 -> F32
    \\step = |x| x + 1.0
    \\bump : F32 -> F32
    \\bump = |x| step(x) * step(x + 2.0)
    \\twice : F32 -> F32
    \\twice = |x| step(step(x))
    \\main = "${Table.describe(bump)} | ${Table.describe(twice)}"
;

// A function that calls itself is a `Call` of its own row.
const staged_recursive_table = table_stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 1.0 + countdown(x - 1.0) else 0.0
    \\main = Table.describe(countdown)
;

// Naming the callee's row rather than inlining it is what lets a recursive
// function describe at all: the walk writes one `Call` and stops.
const staged_recursive_call = stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 1.0 + countdown(x - 1.0) else 0.0
    \\main = Stage.describe(countdown)
;

// V7: what a loop iterates over. Prints `iteration` of every loop node of the root row.
const iteration_stage = stage ++
    \\Iterations :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| {
    \\        first = Code.graph(code).root_row()
    \\        loops = first.nodes.map_with_index(|nd, k| Iterations.of(first, nd, k))
    \\        Str.join_with(loops.keep_if(|text| !text.is_empty()), " ; ")
    \\    }
    \\
    \\    of : Code.Row, Code.Node, U64 -> Str
    \\    of = |row, nd, k| match nd.op {
    \\        ForList(_) | ForRange(_) | Loop(_) => match row.iteration(k.to_u32_wrap()) {
    \\            OverList(l) => "OverList(exits_early=${Iterations.flag(l.exits_early)}, item=${Iterations.read(l.item)}, index=${Iterations.read(l.index)})"
    \\            OverRange(l) => "OverRange(inclusive=${Iterations.flag(l.inclusive)}, exits_early=${Iterations.flag(l.exits_early)}, index=${Iterations.read(l.index)})"
    \\            General => "General"
    \\        }
    \\        _ => ""
    \\    }
    \\
    \\    flag : Bool -> Str
    \\    flag = |value| if value "True" else "False"
    \\
    \\    read : [Read(Code.Val), Unread] -> Str
    \\    read = |value| match value {
    \\        Read(_) => "Read"
    \\        Unread => "Unread"
    \\    }
    \\}
    \\
;

const staged_iteration_list = iteration_stage ++
    \\total : List(U64) -> U64
    \\total = |xs| {
    \\    var $sum = 0
    \\    for x in xs {
    \\        $sum = $sum + x
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_iter = iteration_stage ++
    \\total : List(U64) -> U64
    \\total = |xs| {
    \\    var $sum = 0
    \\    for x in xs.iter() {
    \\        $sum = $sum + x
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_index_while = iteration_stage ++
    \\total : List(U64) -> U64
    \\total = |xs| {
    \\    var $i = 0
    \\    var $sum = 0
    \\    while $i < xs.len() {
    \\        $sum = $sum + (xs.get($i) ?? 0)
    \\        $i = $i + 1
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_break = iteration_stage ++
    \\total : List(U64) -> U64
    \\total = |xs| {
    \\    var $sum = 0
    \\    for x in xs {
    \\        if x > 100 {
    \\            break
    \\        }
    \\        $sum = $sum + x
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_range = iteration_stage ++
    \\total : U64 -> U64
    \\total = |n| {
    \\    var $sum = 0
    \\    for i in 0..<n {
    \\        $sum = $sum + i
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_counter_while = iteration_stage ++
    \\total : U64 -> U64
    \\total = |n| {
    \\    var $i = 0
    \\    var $sum = 0
    \\    while $i < n {
    \\        $sum = $sum + $i
    \\        $i = $i + 1
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_inclusive = iteration_stage ++
    \\total : U64 -> U64
    \\total = |n| {
    \\    var $sum = 0
    \\    for i in 0..=n {
    \\        $sum = $sum + i
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_general = iteration_stage ++
    \\total : U64 -> U64
    \\total = |n| {
    \\    var $i = 0
    \\    var $sum = 0
    \\    while $i < n {
    \\        $sum = $sum + $i
    \\        $i = $i + 2
    \\    }
    \\    $sum
    \\}
    \\main = Iterations.describe(total)
;

const staged_iteration_tail_call = iteration_stage ++
    \\go : U64, U64, U64 -> U64
    \\go = |acc, i, n| if i < n go(acc + i, i + 1, n) else acc
    \\total : U64 -> U64
    \\total = |n| go(0, 0, n)
    \\main = Iterations.describe(total)
;

// A function whose every call to itself is the value of a path of its body
// is a loop (N12): the call becomes `continue` and the other paths `break`.
const staged_tail_call = stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 countdown(x - 1.0) else x
    \\main = Stage.describe(countdown)
;

// `find` is called from one place, which the graph view inlines, except that
// its loop can end the row in `Return`: inlined, that `Return` would end
// `twice` and skip the `* 2`. So `find` stays a row and `twice` calls it.
const staged_loop_return_call = stage ++
    \\find : List(U8), U8 -> U8
    \\find = |xs, a| {
    \\    for x in xs {
    \\        if x == a {
    \\            return x
    \\        }
    \\    }
    \\    a + 1
    \\}
    \\twice : List(U8), U8 -> U8
    \\twice = |xs, a| find(xs, a) * 2
    \\main = Stage.describe(twice)
;

// A derived `==` over a tag union is a `Switch` on the left operand, with a
// `Switch` on the right one in each arm: the arm that matches compares the
// payloads, and every other arm is `False`.
const staged_derived_eq = stage ++
    \\same : [Red, Green(U8)], [Red, Green(U8)] -> Bool
    \\same = |a, b| a == b
    \\main = Stage.describe(same)
;

// A derived `==` over a nominal compares its backing: each operand is
// unwrapped, and the comparison is the one of the tag union behind it.
const staged_derived_eq_nominal = stage ++
    \\
    \\Color := [Red, Green].{
    \\    is_eq : _
    \\}
    \\
    \\same : Color, Color -> Bool
    \\same = |a, b| a == b
    \\main = Stage.describe(same)
;

// `List.get` returns `Try(a, [OutOfBounds]*)`, and the checker closes that
// error row at the call without rewriting it to `[]`: it marks the variable it
// solved instead. The walk reads the mark, so indexing a list describes.
const staged_list_index = stage ++
    \\
    \\first : List(U64) -> U64
    \\first = |xs| match xs.get(0) {
    \\    Ok(v) => v
    \\    Err(_e) => 0
    \\}
    \\main = Stage.describe(first)
;

// A reified function that hands back a nullary tag.
const staged_nullary_tag_result = stage ++
    \\
    \\probe : U64 -> [Red]
    \\probe = |_n| Red
    \\main = Stage.describe(probe)
;

// An empty list and an empty record are the aggregate each node already
// builds, with nothing in it.
const staged_empty_aggregate = stage ++
    \\
    \\no_items : U64 -> List(U64)
    \\no_items = |_n| []
    \\
    \\no_fields : U64 -> {}
    \\no_fields = |_n| {}
    \\main = "${Stage.describe(no_items)} ; ${Stage.describe(no_fields)}"
;

// A top-level value read from a staged body is the value it holds. The name
// never reaches the description, so a translator has no name to resolve and
// the reified body stays closed over nothing.
const staged_top_level_constant = stage ++
    \\threshold = 2.0.F32
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * threshold
    \\main = Stage.describe(scale)
;

// A value another module exports folds the same way, read through that
// module's own tables.
const staged_imported_constant = stage ++
    \\import Limits
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * Limits.ceiling
    \\main = Stage.describe(scale)
;

// An aggregate folds whole, so a field read of a top-level record folds to
// the field the definition wrote.
const staged_constant_record = stage ++
    \\settings = { gain: 3.0.F32, bias: 0.5.F32 }
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * settings.gain
    \\main = Stage.describe(scale)
;

// A name as a template argument is the value it holds, which is the same
// resolution step read from the other refusal.
const staged_constant_template_argument = stage ++
    \\factor = 4.0.F32
    \\
    \\scaled : F32 -> Code(F32 -> F32)
    \\scaled = |k| |x| x * k
    \\main = Stage.describe(scaled(factor))
;

// A top-level value that has to be computed folds to the computation its
// definition wrote, so the description needs no value the compiler evaluates.
const staged_computed_constant = stage ++
    \\limit = 7.0.F32 * 2.0.F32
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * limit
    \\main = Stage.describe(scale)
;

// A computed value that reads another top-level value folds that one in turn.
const staged_constant_from_constant = stage ++
    \\xs = [1.0.F32, 2.0.F32, 3.0.F32]
    \\count = xs.len()
    \\
    \\widen : U64 -> U64
    \\widen = |n| n + count
    \\main = Stage.describe(widen)
;

// A computed value another module exports folds the same way.
const staged_imported_computed_constant = stage ++
    \\import Limits
    \\
    \\scale : F32 -> F32
    \\scale = |x| x * Limits.ceiling
    \\main = Stage.describe(scale)
;

// A computed value that is a function is the definition it was written as,
// built where the name stands. `make(2.0)` is the call of a definition that
// hands back a function, so the call on `doubler` and the definition are one
// `Call` of the lambda's row, the capture first and the argument after.
const staged_function_constant = stage ++
    \\make : F32 -> (F32 -> F32)
    \\make = |k| |x| x * k
    \\
    \\doubler = make(2.0.F32)
    \\
    \\scale : F32 -> F32
    \\scale = |x| doubler(x)
    \\main = Stage.describe(scale)
;

// A capture that is itself a function follows the same rule: `inc` is a
// definition, so it is the row `twice` calls, and `quad` reads as `twice(inc)`.
const staged_function_constant_capture = stage ++
    \\twice : (F32 -> F32) -> (F32 -> F32)
    \\twice = |f| |x| f(f(x))
    \\
    \\inc : F32 -> F32
    \\inc = |x| x + 1.0.F32
    \\
    \\quad = twice(inc)
    \\
    \\bump : F32 -> F32
    \\bump = |x| quad(x)
    \\main = Stage.describe(bump)
;

// A name read twice describes the same row twice, and a name used as a value
// passes the function the definition computes.
const staged_function_constant_twice = stage ++
    \\make : F32 -> (F32 -> F32)
    \\make = |k| |x| x * k
    \\
    \\doubler = make(2.0.F32)
    \\
    \\both : F32 -> F32
    \\both = |x| doubler(x) + doubler(x + 1.0.F32)
    \\main = Stage.describe(both)
;

// A top-level value that computes a function, used as a value: the function
// is handed to a builtin as the definition it was written as.
const staged_function_constant_value = stage ++
    \\make : F32 -> (F32 -> F32)
    \\make = |k| |x| x * k
    \\
    \\doubler = make(2.0.F32)
    \\
    \\scale_all : List(F32) -> List(F32)
    \\scale_all = |xs| xs.map(doubler)
    \\main = Stage.describe(scale_all)
;

// A top-level value that computes a function and another module exports. The
// module is in the package of the site, so its definition is read there.
const staged_imported_function_constant = stage ++
    \\import Scaler
    \\
    \\scale : F32 -> F32
    \\scale = |x| Scaler.doubler(x) + 1.0.F32
    \\main = Stage.describe(scale)
;

// A site that names a top-level value computing a function has no lambda to
// list parameters from, so it stays refused.
const staged_function_constant_as_site = stage ++
    \\make : F32 -> (F32 -> F32)
    \\make = |k| |x| x * k
    \\
    \\doubler = make(2.0.F32)
    \\main = Stage.describe(doubler)
;

// A top-level name bound to another function is an exact alias. The checker
// records the lookup it forwards to, so a site that names the alias describes
// the function it names.
const staged_alias_at_site = stage ++
    \\add_one : I64 -> I64
    \\add_one = |n| n + 1
    \\
    \\same_thing : I64 -> I64
    \\same_thing = add_one
    \\main = Stage.describe(same_thing)
;

// A call through an alias calls the row of the function the alias names.
const staged_alias_called = stage ++
    \\add_one : I64 -> I64
    \\add_one = |n| n + 1
    \\
    \\same_thing : I64 -> I64
    \\same_thing = add_one
    \\
    \\twice : I64 -> I64
    \\twice = |x| same_thing(x) * 2
    \\main = Stage.describe(twice)
;

// An alias of an alias forwards through both to the one function.
const staged_alias_of_alias = stage ++
    \\add_one : I64 -> I64
    \\add_one = |n| n + 1
    \\
    \\same_thing : I64 -> I64
    \\same_thing = add_one
    \\
    \\again : I64 -> I64
    \\again = same_thing
    \\
    \\both : I64 -> I64
    \\both = |x| again(x) + add_one(x)
    \\main = Stage.describe(both)
;

// An alias another module exports, named at a site.
const staged_imported_alias_at_site = stage ++
    \\import Steps
    \\
    \\main = Stage.describe(Steps.same_thing)
;

// An alias another module exports, called inside a described function.
const staged_imported_alias_called = stage ++
    \\import Steps
    \\
    \\twice : I64 -> I64
    \\twice = |x| Steps.same_thing(x) * 2
    \\main = Stage.describe(twice)
;

const steps_module =
    \\Steps :: {}.{
    \\    add_one : I64 -> I64
    \\    add_one = |n| n + 1
    \\
    \\    same_thing : I64 -> I64
    \\    same_thing = add_one
    \\}
;

// `??` canonicalizes to a match on the `Try`, so it describes as a `Switch`
// whose `Ok` arm reads the payload and whose `Err` arm is the default.
const staged_default_operand = stage ++
    \\pick : Try(F32, [Bad]), F32 -> F32
    \\pick = |t, fallback| t ?? fallback
    \\main = Stage.describe(pick)
;

// `p as name` binds the value the pattern matched, so a read through the name
// is a read of that value.
const staged_as_pattern = stage ++
    \\Pair := { a : F32, b : F32 }
    \\
    \\first : Pair -> F32
    \\first = |p| match p {
    \\    Pair.{ a: _, b: _ } as whole => whole.a
    \\}
    \\main = Stage.describe(first)
;

// A literal written against the author's own type is the conversion the
// checker wrote, and its argument is a `Num.Numeral` the compiler generates.
// The walk refuses a conversion whose argument the compiler generates.
const staged_custom_numeral = stage ++
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

const staged_custom_quote = stage ++
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

// A literal pattern of the author's own type tests the checker's equality of
// the pattern's binder with the converted literal, and each alternative
// converts its own literal.
const staged_custom_literal_pattern = stage ++
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
// call on the same builtin takes, so the two spellings describe as one `Prim`.
// `plain` and `method` are the same function written two ways, and the stage
// prints one string twice.
const staged_builtin_call = stage ++
    \\plain : F32 -> F32
    \\plain = |x| if Str.is_empty(F32.to_str(x)) x else 0.0.F32
    \\method : F32 -> F32
    \\method = |x| if x.to_str().is_empty() x else 0.0.F32
    \\main = "${Stage.describe(plain)} | ${Stage.describe(method)}"
;

// A builtin is named and nothing more: no row is written for it, because a
// translator resolves the name against what its own target provides rather
// than against a body written in Roc.
const staged_builtin_call_table = table_stage ++
    \\pick : F32 -> F32
    \\pick = |x| if Str.is_empty(F32.to_str(x)) x else 0.0.F32
    \\main = Table.describe(pick)
;

// A string literal of more than one segment is one `Str.concat` of its
// segments. An empty segment joins nothing, so `"${s}"` describes as the value
// alone.
const staged_interpolation = stage ++
    \\parts : F32 -> F32
    \\parts = |x| if Str.is_empty("p${x.to_str()}q") x else 0.0.F32
    \\only : F32 -> F32
    \\only = |x| if Str.is_empty("${x.to_str()}") x else 0.0.F32
    \\main = "${Stage.describe(parts)} | ${Stage.describe(only)}"
;

// An interpolated literal of the author's own type applies the assembler its
// `from_interpolation` hands back while the compiler runs. The segments it
// takes are an operand the compiler generates, which the walk refuses.
const staged_custom_interpolation = stage ++
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

// A top-level value keeps its own union, and each use reads it at the union
// the use reads (design.md "Row Coercion Primitive"). The value folds into the
// use at the wider union, so the `match` on it is decided as it would be if
// the tag were written in place.
const staged_widened_value = stage ++
    \\mode = Fast
    \\
    \\pick : F32 -> F32
    \\pick = |x| match mode {
    \\    Fast => x
    \\    Slow => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// A function whose body closes the union its annotation leaves open hands back
// its own union, and the caller reads it at a wider union. The call's value is
// not known, and it reaches the `match` by its tag names, with no node between.
// The switch has the arms of the tags the call's own union holds, so the `Huge`
// arm, which the value cannot reach, is dropped.
const staged_widened_call = stage ++
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

// A record update has no node of its own. Every field of the result is either
// one the update wrote or one read out of the subject, so a read of a field of
// the result folds to that field.
const staged_record_update = stage ++
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

// A subject that is not a name folds the same way: each field read is the
// field the literal wrote.
const staged_record_update_binds = stage ++
    \\move : F32 -> F32
    \\move = |v| {
    \\    moved = { ..{ x: v, y: 1.0 }, y: 2.0 }
    \\    moved.x + moved.y
    \\}
    \\main = Stage.describe(move)
;

// A record literal that unsets an optional field is a `Record` that leaves
// the member out; the record's type says it may be absent.
const staged_unset_field = stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\pick : F32 -> Cfg
    \\pick = |v| {
    \\    c : Cfg
    \\    c = { a: v, b: _ }
    \\    c
    \\}
    \\main = Stage.describe(pick)
;

// A record literal that leaves out an optional field leaves the member unset,
// and the `.?` read of it is the node it is: the stage learns the field is
// absent from the record's `Record` node, which lists the fields it sets.
const staged_optional_field = stage ++
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
const staged_record_rest = stage ++
    \\pick : { x : F32, y : F32 } -> F32
    \\pick = |p| match p {
    \\    { x, .. } => x
    \\}
    \\main = Stage.describe(pick)
;

// List patterns describe as a `Switch` on the length and element reads: an
// exact length is a literal key, and a rest is a length comparison. A pattern
// that an earlier one covers is never reached and has no arm.
const staged_list_pattern = stage ++
    \\pick : List(F32) -> F32
    \\pick = |l| match l {
    \\    [a, b] => a - b
    \\    [a, .., b] => a + b
    \\    [a, .. as mid, b] => a * b
    \\    _ => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// A string pattern with interpolation is the decisions and reads Roc makes
// for it: the prefix test, then a split at the first place each delimiter
// appears, and an exact end that leaves no text.
const staged_str_pattern = stage ++
    \\pick : Str -> Str
    \\pick = |s| match s {
    \\    "a${head}b${_}" => head
    \\    "${tail}z" => tail
    \\    _ => s
    \\}
    \\main = Stage.describe(pick)
;

// A tag union whose row nothing closed has the variants the function names
// and no others, the way Monotype seals the row it lowers.
const staged_open_tag_union = stage ++
    \\pick : [Red, Green, ..], F32 -> F32
    \\pick = |c, x| match c {
    \\    Red => x
    \\    Green => 2.0
    \\    _ => 0.0
    \\}
    \\main = Stage.describe(pick)
;

// An unset field is a member the `Record` leaves out, and the record's type
// says it may be absent. A field the literal leaves out says the same.
const staged_unset_and_omitted = stage ++
    \\Cfg : { a : F32, b ?: F32, c ?: F32 }
    \\pick : F32 -> Cfg
    \\pick = |v| {
    \\    first : Cfg
    \\    first = { a: v, b: _, c: 1.0 }
    \\    second : Cfg
    \\    second = { a: v }
    \\    if v < 1.0 first else second
    \\}
    \\main = Stage.describe(pick)
;

// A record update takes an optional field the update did not write from its
// subject if the subject holds it: a switch on the subject's own `Try`.
const staged_update_optional = stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\bump : Cfg -> Cfg
    \\bump = |cfg| { ..cfg, a: 1.0 }
    \\main = Stage.describe(bump)
;

// An update that unsets the optional field does not read the subject for it.
const staged_update_unsets = stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\clear : Cfg -> Cfg
    \\clear = |cfg| { ..cfg, b: _ }
    \\main = Stage.describe(clear)
;

// A `.?` before the last segment is a switch on its own `Try`: the first
// missing field is the `Err` of the whole path, and what follows rides in `Ok`.
const staged_optional_path = stage ++
    \\Inner : { depth : F32 }
    \\Outer : { inner ?: Inner, size : F32 }
    \\depth_of : Outer -> Try(F32, [MissingField])
    \\depth_of = |o| o.?inner.depth
    \\main = Stage.describe(depth_of)
;

// The same path ending in an optional segment: the last `Try` is the path's.
const staged_optional_path_chain = stage ++
    \\Leaf : { note ?: F32 }
    \\Outer : { leaf ?: Leaf, size : F32 }
    \\note_of : Outer -> Try(F32, [MissingField])
    \\note_of = |o| o.?leaf.?note
    \\main = Stage.describe(note_of)
;

// A `..` that binds a name is the record of the fields the pattern does not
// name, read out of the matched record.
const staged_record_rest_named = stage ++
    \\pick : { x : F32, y : F32, z : F32 } -> F32
    \\pick = |p| match p {
    \\    { x, ..others } => x + others.y + others.z
    \\}
    \\main = Stage.describe(pick)
;

// A rest that binds a name over a record with an optional field carries the
// field when the matched record holds it.
const staged_record_rest_optional = stage ++
    \\Cfg : { a : F32, b ?: F32, c : F32 }
    \\drop_a : Cfg -> { b ?: F32, c : F32 }
    \\drop_a = |cfg| match cfg {
    \\    { a: _, ..others } => others
    \\}
    \\main = Stage.describe(drop_a)
;

// A string pattern that ends in a capture takes the text that is left.
const staged_str_pattern_tail = stage ++
    \\pick : Str -> Str
    \\pick = |s| match s {
    \\    "users/${id}" => id
    \\    _ => ""
    \\}
    \\main = Stage.describe(pick)
;

/// Staging cases, consumed by the parallel runner through `eval_tests.zig`.
// A translator whose result is a `Code.Bound` receives what a lambda reads
// from around itself as input slots (roc-reify-proposal.md section 10.1). It
// runs once, while the compiler runs, and prints the description with the
// number of slots; the values arrive when the program runs.
const bind = stage ++
    \\Bind :: {}.{
    \\    render : Code(f) -> Code.Bound(Str)
    \\    render = |code| {
    \\        graph = Code.graph(code)
    \\        Code.bound(code, "${Stage.root(code)} / ${graph.slots().len().to_str()} slots")
    \\    }
    \\
    \\    shown : Code.Bound(Str) -> Str
    \\    shown = |bound| "${bound.value()} / ${Bind.all(bound.inputs())}"
    \\
    \\    value : Code.Value -> Str
    \\    value = |v| match v {
    \\        Int(i) => "Int(${i.to_str()})"
    \\        U128(u) => "U128(${u.to_str()})"
    \\        Frac(f) => "Frac(${f.to_str()})"
    \\        Dec(d) => "Dec(${d.to_str()})"
    \\        Bool(b) => if b "True" else "False"
    \\        Str(text) => "'${text}'"
    \\        Record(vs) => "{${Bind.all(vs)}}"
    \\        Tuple(vs) => "(${Bind.all(vs)})"
    \\        List(vs) => "[${Bind.all(vs)}]"
    \\        Tag(name, vs) => "${name}(${Bind.all(vs)})"
    \\        Wrap(inner) => "Wrap(${Bind.value(inner)})"
    \\    }
    \\
    \\    all : List(Code.Value) -> Str
    \\    all = |vs| Str.join_with(vs.map(Bind.value), ", ")
    \\}
    \\
;

// A parameter of the function around the lambda is a slot. The function is
// described once; each call gives the program the value of its own argument.
const bound_parameter = bind ++
    \\scaled : U16 -> Str
    \\scaled = |n| Bind.shown(Bind.render(|x| n + x))
    \\main = "${scaled(7)} | ${scaled(9)}"
;

// A slot is a name with the fields it reads, so `order.price` is one slot and
// `order` is none. Each slot's value follows its type.
const bound_projections = bind ++
    \\Money := { cents : I64 }
    \\
    \\Order : { price : I64, tags : List(Str), status : [Open, Closed(U8)], limit : Money, ratio : F32 }
    \\
    \\check : Order -> Str
    \\check = |order| Bind.shown(Bind.render(|x| (order.price + x, order.tags, order.status, order.limit, order.ratio)))
    \\
    \\main = check({ price: 5, tags: ["a", "b"], status: Closed(3), limit: Money.({ cents: 250 }), ratio: 0.5 })
;

// A slot whose type is a recursive nominal: each value of the type is built
// by one helper, which reaches itself again.
const bound_recursive = bind ++
    \\Chain := [End, Link(I64, Chain)]
    \\
    \\paired : Chain -> Str
    \\paired = |chain| Bind.shown(Bind.render(|x| (1.I64 + x, chain)))
    \\
    \\main = paired(Chain.Link(1, Chain.Link(2, Chain.End)))
;

// A `var` can be written again before the call, so it is no slot.
const bound_var = bind ++
    \\counted : U16 -> Str
    \\counted = |n| {
    \\    var $total = n
    \\    $total = $total + 1
    \\    Bind.shown(Bind.render(|x| $total + x))
    \\}
    \\main = counted(1)
;

// A function value has no `Code.Value`.
const bound_function = bind ++
    \\applied : (I64 -> I64) -> Str
    \\applied = |f| Bind.shown(Bind.render(|x| f(x)))
    \\main = applied(|y| y + 1)
;

// A translator whose result is not a `Code.Bound` is refused the read.
const unbound_capture = stage ++
    \\scaled : U16 -> Str
    \\scaled = |n| Stage.describe(|x| n + x)
    \\main = scaled(7)
;

pub const tests = [_]TestCase{
    .{
        .name = "staging - a staged function's body becomes a description the stage reads",
        .source_kind = .module,
        .source = staged_binop,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 2)\"" },
    },
    .{
        .name = "staging - a binding the staged body reads twice stays one shared node",
        .source_kind = .module,
        .source = staged_let,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n1 = Num.F32.times(p0, 2); Num.F32.plus(n1, n1) }\"" },
    },
    .{
        .name = "staging - a generic callee is one row per instantiation",
        .source_kind = .module,
        .source = staged_generic_instantiations,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> U64 Num.U64.plus(Num.U64.plus(Num.U64.plus(List.len(r1(p0)), List.len(r1(Num.F32.plus(p0, 1)))), List.len(r2('s'))), List.len(r2('t'))) ; r1 = |F32| -> List(F32) [p0] ; r2 = |Str| -> List(Str) [p0]\"" },
    },
    .{
        .name = "staging - a nested generic callee is keyed by the outer instantiation",
        .source_kind = .module,
        .source = staged_generic_nested,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> U64 Num.U64.plus(List.len(r1(p0, Num.F32.plus(p0, 1))), List.len(r1(Num.F32.plus(p0, 2), p0))) ; r1 = |F32, F32| -> List(F32) List.concat(r2(p0), r2(p1)) ; r2 = |F32| -> List(F32) [p0]\"" },
    },
    .{
        .name = "staging - a generic callee is fixed through a record parameter",
        .source_kind = .module,
        .source = staged_generic_record,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Str Str.concat(Num.F32.to_str(r1(p0)), r2('s'), Num.F32.to_str(r1(Num.F32.plus(p0, 1))), r2('t')) ; r1 = |F32| -> F32 p0 ; r2 = |Str| -> Str p0\"" },
    },
    .{
        .name = "staging - a where-constrained callee names the type the call fixed",
        .source_kind = .module,
        .source = staged_generic_where,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Str Num.F32.to_str(p0) | r0 = |F32| -> Str Num.F32.to_str(p0)\"" },
    },
    .{
        .name = "staging - a lambda in a generic callee describes at each instantiation",
        .source_kind = .module,
        .source = staged_generic_lambdas,
        .expected = .{ .inspect_str = "\"r0 = |List(F32), List(Str)| -> U64 Num.U64.plus(Num.U64.plus(List.len(List.map(List.map(p0, closure r1('k')), closure r2())), List.len(List.map(List.map(p1, closure r3(1)), closure r4()))), List.len(List.map([p0], closure r5()))) ; r1 = |Str, F32| -> (F32, Str) (p1, p0) ; r2 = |(F32, Str)| -> F32 p0.0 ; r3 = |F32, Str| -> (Str, F32) (p1, p0) ; r4 = |(Str, F32)| -> Str p0.0 ; r5 = |List(F32)| -> List((F32, F32)) List.map(p0, closure r6()) ; r6 = |F32| -> (F32, F32) (p0, p0)\"" },
    },
    .{
        .name = "staging - a lambda in a where-constrained generic callee dispatches at the fixed type",
        .source_kind = .module,
        .source = staged_generic_lambda_where,
        .expected = .{ .inspect_str = "\"r0 = |List(U16)| -> U64 Num.U64.plus(List.len(List.map(p0, closure r1())), List.len(List.map(p0, closure r2()))) ; r1 = |U16| -> U16 Num.U16.plus(p0, 1) ; r2 = |U16| -> (U16, U16) (p0, p0)\"" },
    },
    .{
        .name = "staging - an arithmetic parameter no literal pins describes at Dec",
        .source_kind = .module,
        .source = staged_numeric_default,
        .expected = .{ .inspect_str = "\"r0 = |Dec| -> Dec Num.Dec.times(p0, 2.0) | r0 = |Dec, Dec| -> Dec Num.Dec.plus(p0, p1) | r0 = |Dec| -> Dec Num.Dec.minus(p0, 1.0)\"" },
    },
    .{
        .name = "staging - a literal of an unannotated helper describes at the type each use fixed",
        .source_kind = .module,
        .source = staged_unannotated_literal,
        .expected = .{ .inspect_str = "\"r0 = |Dec| -> Dec Num.Dec.times(p0, 3.0) | r0 = |U8| -> U8 Num.U8.times(p0, 3)\"" },
    },
    .{
        .name = "staging - a lambda written at the site calls unannotated helpers at the types it fixes",
        .source_kind = .module,
        .source = staged_inline_unannotated_calls,
        .expected = .{ .inspect_str = "\"r0 = |Str| -> U64 Num.U64.plus(Str.count_utf8_bytes(p0), 1) | r0 = |Str| -> List(U64) List.map([Str.count_utf8_bytes(p0)], closure r1()) ; r1 = |U64| -> U64 Num.U64.plus(p0, 1) | r0 = |Str| -> U64 r1(r1(Str.count_utf8_bytes(p0))) ; r1 = |U64| -> U64 Num.U64.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - an unannotated helper calls another at the evidence its caller supplied",
        .source_kind = .module,
        .source = staged_generic_calls_generic,
        .expected = .{ .inspect_str = "\"r0 = |Str| -> U64 Num.U64.plus(Str.count_utf8_bytes(p0), 1) | r0 = |Str| -> List(U64) List.map([Str.count_utf8_bytes(p0)], closure r1()) ; r1 = |U64| -> U64 Num.U64.times(p0, 2) | r0 = |Str| -> List(U64) List.map([Str.count_utf8_bytes(p0)], closure r1()) ; r1 = |U64| -> U64 Num.U64.times(p0, 2) | r0 = |Str| -> U64 Num.U64.plus(Str.count_utf8_bytes(p0), 1) | r0 = |Str| -> List(U64) List.map([Str.count_utf8_bytes(p0)], closure r1()) ; r1 = |U64| -> U64 Num.U64.times(p0, 2)\"" },
    },
    .{
        .name = "staging - a lambda that captures a fixed function parameter names its definition",
        .source_kind = .module,
        .source = staged_bound_capture,
        .expected = .{ .inspect_str = "\"r0 = |List(I64)| -> (List(I64), List(I64), List(I64)) (List.map(p0, closure r1()), List.map(p0, closure r2()), List.map(p0, closure r3())) ; r1 = |I64| -> I64 Num.I64.times(p0, 3) ; r2 = |I64| -> I64 Num.I64.plus(p0, 1) ; r3 = |I64| -> I64 r4(r4(p0)) ; r4 = |I64| -> I64 Num.I64.minus(p0, 1)\"" },
    },
    .{
        .name = "staging - a type-level statement in a block leaves no node behind",
        .source_kind = .module,
        .source = staged_type_statement,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(Num.F32.times(p0, 2), 1)\"" },
    },
    .{
        .name = "staging - a type dispatch names the type the instantiation fixed",
        .source_kind = .module,
        .source = staged_type_dispatch,
        .expected = .{ .inspect_str = "\"r0 = |Token| -> Str unwrap(p0).raw\"" },
    },
    .{
        .name = "staging - a method call names a row the way a plain call does",
        .source_kind = .module,
        .source = staged_method_definition,
        .expected = .{ .inspect_str = "\"r0 = |Token, Token| -> Str Str.concat(r1(p0), r1(p1)) ; r1 = |Token| -> Str unwrap(p0).raw\"" },
    },
    .{
        .name = "staging - a parametric nominal reads its backing at its type arguments",
        .source_kind = .module,
        .source = staged_parametric_nominal,
        .expected = .{ .inspect_str = "\"r0 = |Crate| -> Crate derived map(p0, closure r1()) ; r1 = |F32| -> F32 Num.F32.times(p0, 2)\"" },
    },
    .{
        .name = "staging - a function argument fixes the parameter it is passed for",
        .source_kind = .module,
        .source = staged_function_argument,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n4 = Num.F32.plus(p0, 1); Num.F32.plus(Num.F32.plus(Num.F32.plus(r1(p0), r2(p0)), r1(n4)), r2(n4)) } ; r1 = |F32| -> F32 Num.F32.times(p0, 2) ; r2 = |F32| -> F32 Num.F32.times(p0, 3) | r0 = |F32| -> F32 Num.F32.times(r1(p0), r1(Num.F32.plus(p0, 2))) ; r1 = |F32| -> F32 Num.F32.minus(p0, 1)\"" },
    },
    .{
        .name = "staging - a lambda a block bound is lifted into a row of its own",
        .source_kind = .module,
        .source = staged_local_lambda,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(r1(p0), r1(Num.F32.plus(p0, 1))) ; r1 = |F32| -> F32 Num.F32.times(p0, 2) | r0 = |F32| -> F32 Num.F32.plus(r1(1, p0), r1(2, p0)) ; r1 = |F32, F32| -> F32 Num.F32.times(p0, p1)\"" },
    },
    .{
        .name = "staging - a curried definition and the call that runs it are one row",
        .source_kind = .module,
        .source = staged_curried_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(r1(p0, 2), r1(p0, 3)) ; r1 = |F32, F32| -> F32 Num.F32.times(p0, p1) | r0 = |F32| -> F32 Num.F32.plus(r1(p0, 2), r1(Num.F32.plus(p0, 1), 2)) ; r1 = |F32, F32| -> F32 Num.F32.times(p0, p1)\"" },
    },
    .{
        .name = "staging - a derived codec folds its construction and its use into one node",
        .source_kind = .module,
        .source = staged_derived_codec,
        .expected = .{ .inspect_str = "\"r0 = |{ a : Str }| -> Builtin.Try derived encoder_for(Format.(Default()), p0, 0)\"" },
    },
    .{
        .name = "staging - a codec the author wrote describes as a call, not a Derived",
        .source_kind = .module,
        .source = staged_codec_origin,
        .expected = .{ .inspect_str = "\"r0 = |{ a : Str }| -> { a : Str }, U64 -> Builtin.Try derived encoder_for(Format.(Default())) | r0 = |Token| -> Token, U64 -> Builtin.Try closure r1() ; r1 = |Token, U64| -> Builtin.Try Builtin.Try.(Ok(Num.U64.plus(p1, Str.count_utf8_bytes(unwrap(p0).raw))))\"" },
    },
    .{
        .name = "staging - a lambda the staged body returns is a Closure of its own row",
        .source_kind = .module,
        .source = staged_nested_lambda,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 -> F32 closure r1(p0) ; r1 = |F32, F32| -> F32 Num.F32.plus(p0, p1)\"" },
    },
    .{
        .name = "staging - a codec the author wrote runs its own body over the arguments a derived one reads",
        .source_kind = .module,
        .source = staged_codec_applied,
        .expected = .{ .inspect_str = "\"r0 = |{ a : Str }, U64| -> Builtin.Try derived encoder_for(Format.(Default()), p0, p1) | r0 = |Token, U64| -> Builtin.Try Builtin.Try.(Ok(Num.U64.plus(p1, Str.count_utf8_bytes(unwrap(p0).raw))))\"" },
    },
    .{
        .name = "staging - every spelling of inversion describes as one Bool.not",
        .source_kind = .module,
        .source = staged_not_spellings,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Bool Bool.not(Num.F32.is_lt(1, p0)) r0 = |F32| -> Bool Bool.not(Num.F32.is_lt(1, p0)) r0 = |F32| -> Bool Bool.not(Num.F32.is_lt(1, p0))\"" },
    },
    .{
        .name = "staging - a Code parameter handed on is not staged again",
        .source_kind = .module,
        .source = staged_record_field,
        .expected = .{ .inspect_str = "\"r0 = |Point| -> F32 { n0 = unwrap(p0); Num.F32.plus(n0.x, n0.y) }\"" },
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
        .name = "staging - children hands back every region, so a walk reaches guards and loop bodies",
        .source_kind = .module,
        .source = staged_ir_children,
        .expected = .{ .inspect_str = "\"15 nodes, Num.F32.times Num.F32.plus Num.U16.min Num.U16.is_lt Num.F32.plus Num.U16.to_f32 Num.F32.min\"" },
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
        .expected = .{ .inspect_str = "\"r0 = |Color| -> F32 { n0 = unwrap(p0); switch n0 { Blue => 1 | Green => { n3 = n0.Green.0; switch Num.F32.is_lt(0, n3) { False => 0 | True => n3 } } | Red => 1 } }\"" },
    },
    .{
        .name = "staging - a literal, a wildcard and a binder inside a record pattern",
        .source_kind = .module,
        .source = staged_match_patterns,
        .expected = .{ .inspect_str = "\"r0 = |{ a : U8, b : U8 }| -> U8 { n0 = p0.a; switch n0 { 0 => p0.b | _ => n0 } }\"" },
    },
    .{
        .name = "staging - constructing a tag describes as a Tag in its nominal",
        .source_kind = .module,
        .source = staged_make_tag,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Color Color.(Green(p0))\"" },
    },
    .{
        .name = "staging - a recursive nominal is built and matched in a staged body",
        .source_kind = .module,
        .source = staged_recursive_value,
        .expected = .{ .inspect_str = "\"r0 = |Tree| -> Tree { n0 = unwrap(p0); switch n0 { Leaf => { n2 = Tree.(Leaf()); Tree.(Node(n2, n2)) } | Node => Tree.(Node(n0.Node.0, p0)) } }\"" },
    },
    .{
        .name = "staging - and describes as one And node",
        .source_kind = .module,
        .source = staged_and,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Bool and(Num.F32.is_lt(1, p0), Num.F32.is_lt(p0, 2))\"" },
    },
    .{
        .name = "staging - a plain call to a named function is a Call of its row",
        .source_kind = .module,
        .source = staged_plain_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n0 = r1(p0); Num.F32.plus(n0, r1(n0)) } ; r1 = |F32| -> F32 Num.F32.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - a callee whose loop can return stays a row, not inlined",
        .source_kind = .module,
        .source = staged_loop_return_call,
        .expected = .{ .inspect_str = "\"r0 = |List(U8), U8| -> U8 Num.U8.times(r1(p1, p0), 2) ; r1 = |U8, List(U8)| -> U8 { n4 = for_list(p1, switch Num.U8.is_eq(s4.1, p0) { False => continue() | True => return s4.1 }); Num.U8.plus(p0, 1) }\"" },
    },
    .{
        .name = "staging - a recursive call describes, because the callee is named rather than inlined",
        .source_kind = .module,
        .source = staged_recursive_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Num.F32.is_lt(0, p0) { False => 0 | True => Num.F32.plus(1, r0(Num.F32.minus(p0, 1))) }\"" },
    },
    .{
        .name = "staging - a for over a list iterates over the list, reading the item and not the index",
        .source_kind = .module,
        .source = staged_iteration_list,
        .expected = .{ .inspect_str = "\"OverList(exits_early=False, item=Read, index=Unread)\"" },
    },
    .{
        .name = "staging - a for over xs.iter() iterates over the list as the plain for does",
        .source_kind = .module,
        .source = staged_iteration_iter,
        .expected = .{ .inspect_str = "\"OverList(exits_early=False, item=Read, index=Unread)\"" },
    },
    .{
        .name = "staging - a while over the indices of a list iterates over the list, reading the item and not the index",
        .source_kind = .module,
        .source = staged_iteration_index_while,
        .expected = .{ .inspect_str = "\"OverList(exits_early=False, item=Read, index=Unread)\"" },
    },
    .{
        .name = "staging - a for with a break over a list can exit early",
        .source_kind = .module,
        .source = staged_iteration_break,
        .expected = .{ .inspect_str = "\"OverList(exits_early=True, item=Read, index=Unread)\"" },
    },
    .{
        .name = "staging - a for over a range iterates over the range, reading the index",
        .source_kind = .module,
        .source = staged_iteration_range,
        .expected = .{ .inspect_str = "\"OverRange(inclusive=False, exits_early=False, index=Read)\"" },
    },
    .{
        .name = "staging - a counter while iterates over the range as the for does",
        .source_kind = .module,
        .source = staged_iteration_counter_while,
        .expected = .{ .inspect_str = "\"OverRange(inclusive=False, exits_early=False, index=Read)\"" },
    },
    .{
        .name = "staging - a for over an inclusive range says it is inclusive",
        .source_kind = .module,
        .source = staged_iteration_inclusive,
        .expected = .{ .inspect_str = "\"OverRange(inclusive=True, exits_early=False, index=Read)\"" },
    },
    .{
        .name = "staging - a while that steps by 2 is a general loop",
        .source_kind = .module,
        .source = staged_iteration_general,
        .expected = .{ .inspect_str = "\"General\"" },
    },
    .{
        .name = "staging - a tail-recursive function iterates over the range as the for does",
        .source_kind = .module,
        .source = staged_iteration_tail_call,
        .expected = .{ .inspect_str = "\"OverRange(inclusive=False, exits_early=False, index=Read)\"" },
    },
    .{
        .name = "staging - a tail call describes as the loop it is",
        .source_kind = .module,
        .source = staged_tail_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 loop(p0, switch Num.F32.is_lt(0, s5.0) { False => break(s5.0) | True => continue(Num.F32.minus(s5.0, 1)) })\"" },
    },
    .{
        .name = "staging - a callee's description arrives beside the root, once however many calls reach it",
        .source_kind = .module,
        .source = staged_call_table,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n0 = r1(p0); Num.F32.plus(n0, r1(n0)) } ; r1 = |F32| -> F32 Num.F32.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - a callee's row follows the row that first calls it",
        .source_kind = .module,
        .source = staged_call_chain,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.minus(r1(p0), r1(r2(Num.F32.times(p0, 3)))) ; r1 = |F32| -> F32 Num.F32.times(r2(p0), 2) ; r2 = |F32| -> F32 Num.F32.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - two sites reaching one callee each carry a row for it",
        .source_kind = .module,
        .source = staged_call_shared,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(r1(p0), r1(Num.F32.plus(p0, 2))) ; r1 = |F32| -> F32 Num.F32.plus(p0, 1) | r0 = |F32| -> F32 r1(r1(p0)) ; r1 = |F32| -> F32 Num.F32.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - a recursive function is a row of its own table",
        .source_kind = .module,
        .source = staged_recursive_table,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Num.F32.is_lt(0, p0) { False => 0 | True => Num.F32.plus(1, r0(Num.F32.minus(p0, 1))) }\"" },
    },
    .{
        .name = "staging - a derived == over a tag union describes as the match it is",
        .source_kind = .module,
        .source = staged_derived_eq,
        .expected = .{ .inspect_str = "\"r0 = |[Green(U8), Red], [Green(U8), Red]| -> Bool switch p0 { Green => switch p1 { Green => Num.U8.is_eq(p0.Green.0, p1.Green.0) | Red => False } | Red => switch p1 { Green => False | Red => True } }\"" },
    },
    .{
        .name = "staging - a derived == over a nominal compares its unwrapped backing",
        .source_kind = .module,
        .source = staged_derived_eq_nominal,
        .expected = .{ .inspect_str = "\"r0 = |Color, Color| -> Bool { n1 = unwrap(p1); switch unwrap(p0) { Green => switch n1 { Green => True | Red => False } | Red => switch n1 { Green => False | Red => True } } }\"" },
    },
    .{
        .name = "staging - a row the checker closed describes, so List.get describes",
        .source_kind = .module,
        .source = staged_list_index,
        .expected = .{ .inspect_str = "\"r0 = |List(U64)| -> U64 { n2 = unwrap(List.get(p0, 0)); switch n2 { Err => 0 | Ok => n2.Ok.0 } }\"" },
    },
    .{
        .name = "staging - a template's compile-time argument is folded into the description",
        .source_kind = .module,
        .source = staged_template,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 3)\"" },
    },
    .{
        .name = "staging - two calls of one template describe two bodies",
        .source_kind = .module,
        .source = staged_template_twice,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 2) | r0 = |F32| -> F32 Num.F32.times(p0, 7)\"" },
    },
    .{
        .name = "staging - a template takes a list, and a staged body writes one",
        .source_kind = .module,
        .source = staged_list,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, Num.U64.to_f32(List.len([2, 4])))\"" },
    },
    .{
        .name = "staging - a template takes a record, and a field read of it folds",
        .source_kind = .module,
        .source = staged_record_argument,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 3)\"" },
    },
    .{
        .name = "staging - a template folds every argument it names",
        .source_kind = .module,
        .source = staged_template_many,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(Num.F32.times(p0, 2), 5)\"" },
    },
    .{
        .name = "staging - a reified function hands back a nullary tag",
        .source_kind = .module,
        .source = staged_nullary_tag_result,
        .expected = .{ .inspect_str = "\"r0 = |U64| -> [Red] Red()\"" },
    },
    .{
        .name = "staging - an empty list and an empty record describe as the aggregates they are",
        .source_kind = .module,
        .source = staged_empty_aggregate,
        .expected = .{ .inspect_str = "\"r0 = |U64| -> List(U64) [] ; r0 = |U64| -> {} {}\"" },
    },
    .{
        .name = "staging - a top-level value read from a staged body is the value it holds",
        .source_kind = .module,
        .source = staged_top_level_constant,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 2)\"" },
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 7)\"" },
    },
    .{
        .name = "staging - a top-level record folds, and a field read of it folds too",
        .source_kind = .module,
        .source = staged_constant_record,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 3)\"" },
    },
    .{
        .name = "staging - a name as a template argument folds to the value it holds",
        .source_kind = .module,
        .source = staged_constant_template_argument,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 4)\"" },
    },
    .{
        .name = "staging - a computed top-level value folds to the computation it holds",
        .source_kind = .module,
        .source = staged_computed_constant,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 14)\"" },
    },
    .{
        .name = "staging - a computed top-level value reads another one through its definition",
        .source_kind = .module,
        .source = staged_constant_from_constant,
        .expected = .{ .inspect_str = "\"r0 = |U64| -> U64 Num.U64.plus(p0, List.len([1, 2, 3]))\"" },
    },
    .{
        .name = "staging - a computed value another module exports folds the same way",
        .source_kind = .module,
        .source = staged_imported_computed_constant,
        .imports = &.{.{
            .name = "Limits",
            .source =
            \\Limits :: {}.{
            \\    ceiling : F32
            \\    ceiling = 7.0.F32 * 2.0.F32
            \\}
            ,
        }},
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 14)\"" },
    },
    .{
        .name = "staging - a top-level value that computes a function describes as the lambda it holds",
        .source_kind = .module,
        .source = staged_function_constant,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, 2)\"" },
    },
    .{
        .name = "staging - a function captured by a top-level value that computes a function is a row too",
        .source_kind = .module,
        .source = staged_function_constant_capture,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 r1(r1(p0)) ; r1 = |F32| -> F32 Num.F32.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - two calls on a top-level value that computes a function share one row",
        .source_kind = .module,
        .source = staged_function_constant_twice,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(r1(p0, 2), r1(Num.F32.plus(p0, 1), 2)) ; r1 = |F32, F32| -> F32 Num.F32.times(p0, p1)\"" },
    },
    .{
        .name = "staging - a top-level value that computes a function is a function value too",
        .source_kind = .module,
        .source = staged_function_constant_value,
        .expected = .{ .inspect_str = "\"r0 = |List(F32)| -> List(F32) List.map(p0, closure r1(2)) ; r1 = |F32, F32| -> F32 Num.F32.times(p1, p0)\"" },
    },
    .{
        .name = "staging - a top-level value that computes a function and another module exports describes as the lambda it holds",
        .source_kind = .module,
        .source = staged_imported_function_constant,
        .imports = &.{.{
            .name = "Scaler",
            .source =
            \\Scaler :: {}.{
            \\    make : F32 -> (F32 -> F32)
            \\    make = |k| |x| x * k
            \\
            \\    doubler = make(2.0.F32)
            \\}
            ,
        }},
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(Num.F32.times(p0, 2), 1)\"" },
    },
    .{
        .name = "staging - a site that names a top-level value computing a function is refused",
        .source_kind = .module,
        .source = staged_function_constant_as_site,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a site that names an alias describes the function it names",
        .source_kind = .module,
        .source = staged_alias_at_site,
        .expected = .{ .inspect_str = "\"r0 = |I64| -> I64 Num.I64.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - a call through an alias calls the row of the function it names",
        .source_kind = .module,
        .source = staged_alias_called,
        .expected = .{ .inspect_str = "\"r0 = |I64| -> I64 Num.I64.times(Num.I64.plus(p0, 1), 2)\"" },
    },
    .{
        .name = "staging - an alias of an alias forwards to the one function",
        .source_kind = .module,
        .source = staged_alias_of_alias,
        .expected = .{ .inspect_str = "\"r0 = |I64| -> I64 { n1 = Num.I64.plus(p0, 1); Num.I64.plus(n1, n1) }\"" },
    },
    .{
        .name = "staging - a site that names an imported alias describes the function it names",
        .source_kind = .module,
        .source = staged_imported_alias_at_site,
        .imports = &.{.{ .name = "Steps", .source = steps_module }},
        .expected = .{ .inspect_str = "\"r0 = |I64| -> I64 Num.I64.plus(p0, 1)\"" },
    },
    .{
        .name = "staging - a call through an imported alias calls the row of the function it names",
        .source_kind = .module,
        .source = staged_imported_alias_called,
        .imports = &.{.{ .name = "Steps", .source = steps_module }},
        .expected = .{ .inspect_str = "\"r0 = |I64| -> I64 Num.I64.times(Num.I64.plus(p0, 1), 2)\"" },
    },
    .{
        .name = "staging - a default operand describes as a switch on the Try",
        .source_kind = .module,
        .source = staged_default_operand,
        .expected = .{ .inspect_str = "\"r0 = |Builtin.Try, F32| -> F32 { n0 = unwrap(p0); switch n0 { Err => p1 | Ok => n0.Ok.0 } }\"" },
    },
    .{
        .name = "staging - an as pattern reads the value it renames",
        .source_kind = .module,
        .source = staged_as_pattern,
        .expected = .{ .inspect_str = "\"r0 = |Pair| -> F32 unwrap(p0).a\"" },
    },
    .{
        .name = "staging - a numeral of the author's own type names the conversion that makes it",
        .source_kind = .module,
        .source = staged_custom_numeral,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n8 = unwrap(Num.F32.from_numeral(Builtin.Num.Numeral.(Literal({ digits_after_pt: [], digits_after_pt_count: 1, digits_before_pt: bytes[3], is_negative: False })))); Num.F32.times(unwrap(switch n8 { Err => crash('this literal was rejected by its conversion') | Ok => Meters.({ m: n8.Ok.0 }) }).m, p0) }\"" },
    },
    .{
        .name = "staging - a quoted literal of the author's own type names its conversion",
        .source_kind = .module,
        .source = staged_custom_quote,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Str.is_empty('hi') { False => p0 | True => 0 }\"" },
    },
    .{
        .name = "staging - each alternative of a literal pattern carries its own condition",
        .source_kind = .module,
        .source = staged_custom_literal_pattern,
        .expected = .{ .inspect_str = "\"r0 = |Count, F32| -> F32 { n0 = []; n8 = unwrap(r1(Builtin.Num.Numeral.(Literal({ digits_after_pt: n0, digits_after_pt_count: 0, digits_before_pt: bytes[7], is_negative: False })))); switch or(r2(p0, switch n8 { Err => crash('this literal was rejected by its conversion') | Ok => n8.Ok.0 }), { n19 = unwrap(r1(Builtin.Num.Numeral.(Literal({ digits_after_pt: n0, digits_after_pt_count: 0, digits_before_pt: bytes[8], is_negative: False })))); r2(p0, switch n19 { Err => crash('this literal was rejected by its conversion') | Ok => n19.Ok.0 }) }) { False => 0 | True => p1 } } ; r1 = |Builtin.Num.Numeral| -> Builtin.Try { n1 = unwrap(Num.U32.from_numeral(p0)); switch n1 { Err => Builtin.Try.(Err(n1.Err.0)) | Ok => Builtin.Try.(Ok(Count.({ n: n1.Ok.0 }))) } } ; r2 = |Count, Count| -> Bool Num.U32.is_eq(unwrap(p0).n, unwrap(p1).n)\"" },
    },
    .{
        .name = "staging - a plain call to a builtin takes the name a method call on it takes",
        .source_kind = .module,
        .source = staged_builtin_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Str.is_empty(Num.F32.to_str(p0)) { False => 0 | True => p0 } | r0 = |F32| -> F32 switch Str.is_empty(Num.F32.to_str(p0)) { False => 0 | True => p0 }\"" },
    },
    .{
        .name = "staging - a builtin is named, and no row is written for it",
        .source_kind = .module,
        .source = staged_builtin_call_table,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Str.is_empty(Num.F32.to_str(p0)) { False => 0 | True => p0 }\"" },
    },
    .{
        .name = "staging - an interpolated literal describes as the concatenation it is",
        .source_kind = .module,
        .source = staged_interpolation,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Str.is_empty(Str.concat('p', Num.F32.to_str(p0), 'q')) { False => 0 | True => p0 } | r0 = |F32| -> F32 switch Str.is_empty(Num.F32.to_str(p0)) { False => 0 | True => p0 }\"" },
    },
    .{
        .name = "staging - an interpolated literal of the author's own type is refused",
        .source_kind = .module,
        .source = staged_custom_interpolation,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a top-level value folds at the wider union its use reads",
        .source_kind = .module,
        .source = staged_widened_value,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 p0\"" },
    },
    .{
        .name = "staging - a call result of the union its callee's body closed reaches a wider match by name",
        .source_kind = .module,
        .source = staged_widened_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Num.F32.is_lt(p0, 1) { False => 2 | True => p0 }\"" },
    },
    .{
        .name = "staging - a record update folds into the fields its reads use",
        .source_kind = .module,
        .source = staged_record_update,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(p0, 2)\"" },
    },
    .{
        .name = "staging - a record update of a literal subject folds the same way",
        .source_kind = .module,
        .source = staged_record_update_binds,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.plus(p0, 2)\"" },
    },
    .{
        .name = "staging - an unset field is left out, and the type says it may be absent",
        .source_kind = .module,
        .source = staged_unset_field,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> { a : F32, b : F32 } { a: p0 }\"" },
    },
    .{
        .name = "staging - a read of an optional field carries the Try it hands back",
        .source_kind = .module,
        .source = staged_optional_field,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 { n2 = unwrap({ a: p0 }.?b); switch n2 { Err => p0 | Ok => n2.Ok.0 } }\"" },
    },
    .{
        .name = "staging - a record pattern drops a rest that binds nothing",
        .source_kind = .module,
        .source = staged_record_rest,
        .expected = .{ .inspect_str = "\"r0 = |{ x : F32, y : F32 }| -> F32 p0.x\"" },
    },
    .{
        .name = "staging - a list pattern with a rest is a length test and element reads",
        .source_kind = .module,
        .source = staged_list_pattern,
        .expected = .{ .inspect_str = "\"r0 = |List(F32)| -> F32 { n0 = List.len(p0); switch n0 { 2 => Num.F32.minus(item(p0, 0), item(p0, 1)) | _ => switch Num.U64.is_lt(n0, 2) { False => Num.F32.plus(item(p0, 0), item(p0, Num.U64.minus(n0, 1))) | True => 0 } } }\"" },
    },
    .{
        .name = "staging - a string pattern is transcribed step by step",
        .source_kind = .module,
        .source = staged_str_pattern,
        .expected = .{ .inspect_str = "\"r0 = |Str| -> Str switch Str.starts_with(p0, 'a') { False => { n4 = unwrap(Str.split_first(p0, 'z')); switch n4 { Err => p0 | Ok => { n5 = n4.Ok.0; switch Str.is_empty(n5.after) { False => p0 | True => n5.before } } } } | True => { n14 = unwrap(Str.split_first(Str.drop_prefix(p0, 'a'), 'b')); switch n14 { Err => { n17 = unwrap(Str.split_first(p0, 'z')); switch n17 { Err => p0 | Ok => { n18 = n17.Ok.0; switch Str.is_empty(n18.after) { False => p0 | True => n18.before } } } } | Ok => n14.Ok.0.before } } }\"" },
    },
    .{
        .name = "staging - a tag union whose row nothing closed has the variants the function names",
        .source_kind = .module,
        .source = staged_open_tag_union,
        .expected = .{ .inspect_str = "\"r0 = |[Green, Red], F32| -> F32 switch p0 { Green => 2 | Red => p1 }\"" },
    },
    .{
        .name = "staging - an unset field and a field left out are members the record does not set",
        .source_kind = .module,
        .source = staged_unset_and_omitted,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> { a : F32, b : F32, c : F32 } switch Num.F32.is_lt(p0, 1) { False => { a: p0 } | True => { a: p0, c: 1 } }\"" },
    },
    .{
        .name = "staging - a record update takes an optional field from its subject by a switch on its Try",
        .source_kind = .module,
        .source = staged_update_optional,
        .expected = .{ .inspect_str = "\"r0 = |{ a : F32, b : F32 }| -> { a : F32, b : F32 } { n1 = unwrap(p0.?b); switch n1 { Err => { a: 1 } | Ok => { a: 1, b: n1.Ok.0 } } }\"" },
    },
    .{
        .name = "staging - a record update that unsets an optional field reads nothing for it",
        .source_kind = .module,
        .source = staged_update_unsets,
        .expected = .{ .inspect_str = "\"r0 = |{ a : F32, b : F32 }| -> { a : F32, b : F32 } { a: p0.a }\"" },
    },
    .{
        .name = "staging - a path with an optional segment before the last is a switch on its Try",
        .source_kind = .module,
        .source = staged_optional_path,
        .expected = .{ .inspect_str = "\"r0 = |{ inner : { depth : F32 }, size : F32 }| -> Builtin.Try { n1 = unwrap(p0.?inner); switch n1 { Err => Builtin.Try.(Err(MissingField())) | Ok => Builtin.Try.(Ok(n1.Ok.0.depth)) } }\"" },
    },
    .{
        .name = "staging - a path that ends in an optional segment keeps the last Try",
        .source_kind = .module,
        .source = staged_optional_path_chain,
        .expected = .{ .inspect_str = "\"r0 = |{ leaf : { note : F32 }, size : F32 }| -> Builtin.Try { n1 = unwrap(p0.?leaf); switch n1 { Err => Builtin.Try.(Err(MissingField())) | Ok => n1.Ok.0.?note } }\"" },
    },
    .{
        .name = "staging - a record pattern rest that binds a name is the fields the pattern leaves",
        .source_kind = .module,
        .source = staged_record_rest_named,
        .expected = .{ .inspect_str = "\"r0 = |{ x : F32, y : F32, z : F32 }| -> F32 Num.F32.plus(Num.F32.plus(p0.x, p0.y), p0.z)\"" },
    },
    .{
        .name = "staging - a record pattern rest over an optional field carries the field when it is held",
        .source_kind = .module,
        .source = staged_record_rest_optional,
        .expected = .{ .inspect_str = "\"r0 = |{ a : F32, b : F32, c : F32 }| -> { b : F32, c : F32 } { n1 = unwrap(p0.?b); n2 = p0.c; switch n1 { Err => { c: n2 } | Ok => { b: n1.Ok.0, c: n2 } } }\"" },
    },
    .{
        .name = "staging - a string pattern that ends in a capture takes the text that is left",
        .source_kind = .module,
        .source = staged_str_pattern_tail,
        .expected = .{ .inspect_str = "\"r0 = |Str| -> Str switch Str.starts_with(p0, 'users/') { False => '' | True => Str.drop_prefix(p0, 'users/') }\"" },
    },
    .{
        .name = "staging - a translator that returns a Code.Bound receives a captured parameter as an input slot",
        .source_kind = .module,
        .source = bound_parameter,
        .expected = .{ .inspect_str = "\"Num.U16.plus(in0, p0) / 1 slots / Int(7) | Num.U16.plus(in0, p0) / 1 slots / Int(9)\"" },
    },
    .{
        .name = "staging - each field a lambda reads from a captured record is one input slot with the value of its type",
        .source_kind = .module,
        .source = bound_projections,
        .expected = .{ .inspect_str = "\"(Num.I64.plus(in0, p0), in1, in2, in3, in4) / 5 slots / Int(5), ['a', 'b'], Closed(Int(3)), Wrap({Int(250)}), Frac(0.5)\"" },
    },
    .{
        .name = "staging - a captured value of a recursive type is built by a helper that reaches itself",
        .source_kind = .module,
        .source = bound_recursive,
        .expected = .{ .inspect_str = "\"(Num.I64.plus(p0, 1), in0) / 1 slots / Wrap(Link(Int(1), Wrap(Link(Int(2), Wrap(End())))))\"" },
    },
    .{
        .name = "staging - a captured var is refused as an input slot",
        .source_kind = .module,
        .source = bound_var,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a captured function value is refused as an input slot",
        .source_kind = .module,
        .source = bound_function,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a translator that does not return a Code.Bound is refused a captured value",
        .source_kind = .module,
        .source = unbound_capture,
        .expected = .{ .problem = {} },
    },
};
