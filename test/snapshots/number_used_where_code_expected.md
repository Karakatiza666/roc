# META
~~~ini
description=A number where a Code of a function is expected says that a Code describes a function
type=snippet
~~~
# SOURCE
~~~roc
describe : Code(U64 -> U64) -> Str
describe = |_c| "x"

for_code = describe(5)
~~~
# EXPECTED
TYPE MISMATCH - number_used_where_code_expected.md:4:21:4:22
# PROBLEMS
~~~clojure
(reports
	(report
		(severity runtime_error)
		(title "Type Mismatch")
		(region (start 4 21) (end 4 22))
		(headline
			(reflow "This number is being used where a non-number type is needed."))
		(document
			(source-region (file "number_used_where_code_expected.md") (start 4 21) (end 4 22) (annotation error) (line-text "for_code = describe(5)"))
			(line-break)
			(reflow "Other code expects this to have the type:")
			(line-break)
			(line-break)
			(annotation-start code-block)
			(indent 1)
			(text "Code(U64 -> U64)")
			(annotation-end)
			(line-break)
			(reflow "A")
			(reflow " ")
			(annotated emphasis "Code")
			(reflow " ")
			(reflow "describes a function. Write the name of a function, or a lambda, where the")
			(reflow " ")
			(annotated emphasis "Code")
			(reflow " ")
			(reflow "is expected."))))
~~~
# TOKENS
~~~zig
LowerIdent,OpColon,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,OpArrow,UpperIdent,
LowerIdent,OpAssign,OpBar,NamedUnderscore,OpBar,StringStart,StringPart,StringEnd,
LowerIdent,OpAssign,LowerIdent,NoSpaceOpenRound,Int,CloseRound,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-type-anno (name "describe")
			(ty-fn
				(ty-apply
					(ty (name "Code"))
					(ty-fn
						(ty (name "U64"))
						(ty (name "U64"))))
				(ty (name "Str"))))
		(s-decl
			(p-ident (raw "describe"))
			(e-lambda
				(args
					(p-ident (raw "_c")))
				(e-string
					(e-string-part (raw "x")))))
		(s-decl
			(p-ident (raw "for_code"))
			(e-apply
				(e-ident (raw "describe"))
				(e-int (raw "5"))))))
~~~
# FORMATTED
~~~roc
NO CHANGE
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "describe"))
		(e-lambda
			(args
				(p-assign (ident "_c")))
			(e-string
				(e-literal (string "x"))))
		(annotation
			(ty-fn (effectful false)
				(ty-apply (name "Code") (builtin)
					(ty-fn (effectful false)
						(ty-lookup (name "U64") (builtin))
						(ty-lookup (name "U64") (builtin))))
				(ty-lookup (name "Str") (builtin)))))
	(d-let
		(p-assign (ident "for_code"))
		(e-call (constraint-fn-var 508)
			(e-lookup-local
				(p-assign (ident "describe")))
			(e-runtime-error (tag "erroneous_value_expr")))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Code(U64 -> U64) -> Str"))
		(patt (type "Str")))
	(expressions
		(expr (type "Code(U64 -> U64) -> Str"))
		(expr (type "Str"))))
~~~
