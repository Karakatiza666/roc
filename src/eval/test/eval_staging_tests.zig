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
    \\countdown = |x| if x > 0.0 countdown(x - 1.0) else 0.0
    \\main = Table.describe(countdown)
;

// Naming the callee's row rather than inlining it is what lets a recursive
// function describe at all: the walk writes one `Call` and stops.
const staged_recursive_call = stage ++
    \\countdown : F32 -> F32
    \\countdown = |x| if x > 0.0 countdown(x - 1.0) else 0.0
    \\main = Stage.describe(countdown)
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

// A computed value that is a function names no definition, so a call on it
// has no row to name, and the walk refuses it.
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

// A literal pattern of the author's own type is a conversion of a literal the
// compiler generates, so the walk refuses it as it refuses the literal.
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

// A record literal that leaves an optional field unset has no form in the
// normal form, so the walk refuses it.
const staged_unset_field = stage ++
    \\Cfg : { a : F32, b ?: F32 }
    \\pick : F32 -> F32
    \\pick = |v| {
    \\    c : Cfg
    \\    c = { a: v, b: _ }
    \\    c.a
    \\}
    \\main = Stage.describe(pick)
;

// A record literal that leaves out an optional field has no form in the
// normal form, so the walk refuses it before the `.?` read is reached.
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

// A string pattern with interpolation has no form in the normal form, so the
// walk refuses it.
const staged_str_pattern = stage ++
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Str Str.concat(Num.F32.to_str(r1({ v: p0 })), r2({ v: 's' }), Num.F32.to_str(r1({ v: Num.F32.plus(p0, 1) })), r2({ v: 't' })) ; r1 = |{ v : F32 }| -> F32 p0.v ; r2 = |{ v : Str }| -> Str p0.v\"" },
    },
    .{
        .name = "staging - a where-constrained callee names the type the call fixed",
        .source_kind = .module,
        .source = staged_generic_where,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> Str Num.F32.to_str(p0) | r0 = |F32| -> Str Num.F32.to_str(p0)\"" },
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
        .name = "staging - a recursive call describes, because the callee is named rather than inlined",
        .source_kind = .module,
        .source = staged_recursive_call,
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Num.F32.is_lt(0, p0) { False => 0 | True => r0(Num.F32.minus(p0, 1)) }\"" },
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch Num.F32.is_lt(0, p0) { False => 0 | True => r0(Num.F32.minus(p0, 1)) }\"" },
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, Num.F32.times(7, 2))\"" },
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 Num.F32.times(p0, Num.F32.times(7, 2))\"" },
    },
    .{
        .name = "staging - a top-level value that computes a function is refused",
        .source_kind = .module,
        .source = staged_function_constant,
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
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a quoted literal of the author's own type names its conversion",
        .source_kind = .module,
        .source = staged_custom_quote,
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - each alternative of a literal pattern carries its own condition",
        .source_kind = .module,
        .source = staged_custom_literal_pattern,
        .expected = .{ .problem = {} },
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
        .expected = .{ .inspect_str = "\"r0 = |F32| -> F32 switch switch Num.F32.is_lt(p0, 1) { False => Big() | True => Small() } { Big => 2 | Small => p0 }\"" },
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
        .expected = .{ .problem = {} },
    },
    .{
        .name = "staging - a read of an optional field carries the Try it hands back",
        .source_kind = .module,
        .source = staged_optional_field,
        .expected = .{ .problem = {} },
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
        .expected = .{ .problem = {} },
    },
};
