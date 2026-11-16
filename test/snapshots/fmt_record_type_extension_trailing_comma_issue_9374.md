# META
~~~ini
description=Issue 9374 - Formatter must not crash with integer underflow on a record type whose extension has a trailing comma
type=snippet
~~~
# SOURCE
~~~roc
x : { ..a, }
~~~
# EXPECTED
NIL
# PROBLEMS
NIL
# TOKENS
~~~zig
LowerIdent,OpColon,OpenCurly,DoubleDot,LowerIdent,Comma,CloseCurly,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-type-anno (name "x")
			(ty-record
				(ty-record-ext
					(ty-var (raw "a")))))))
~~~
# FORMATTED
~~~roc
x : {
	..a,
}
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "x"))
		(e-anno-only (kind "intrinsic"))
		(annotation
			(ty-record))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "{ ..a }")))
	(expressions
		(expr (type "{ ..a }"))))
~~~
