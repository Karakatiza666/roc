# META
~~~ini
description=A Code may name a function parameter's type or what a function returns, and nothing else
type=snippet
~~~
# SOURCE
~~~roc
holder : { staged : Code(F32 -> F32) } -> Str
holder = |_r| "x"

nested : (Str -> Code(F32 -> F32)) -> Str
nested = |_f| "x"

lister : List(Code(F32 -> F32)) -> Str
lister = |_l| "x"

accepted : Code(F32 -> F32) -> Str
accepted = |_c| "x"

template : F32 -> Code(F32 -> F32)
template = |factor| |x| x * factor
~~~
# EXPECTED
CODE IS NOT ALLOWED HERE - staged_code_outside_staged_position.md:1:21:1:37
CODE IS NOT ALLOWED HERE - staged_code_outside_staged_position.md:4:18:4:34
CODE IS NOT ALLOWED HERE - staged_code_outside_staged_position.md:7:15:7:31
# PROBLEMS
~~~clojure
(reports
	(report
		(severity runtime_error)
		(title "Code Is Not Allowed Here")
		(region (start 1 21) (end 1 37))
		(headline
			(reflow "A Code can name a function's parameter, or what a function returns."))
		(document
			(source-region (file "staged_code_outside_staged_position.md") (start 1 21) (end 1 37) (annotation error) (line-text "holder : { staged : Code(F32 -> F32) } -> Str"))
			(line-break)
			(reflow "A")
			(reflow " ")
			(annotated emphasis "Code")
			(reflow " ")
			(reflow "exists only while the compiler runs, so it names a function")
			(reflow " ")
			(reflow "parameter, which takes a description, or what a function returns,")
			(reflow " ")
			(reflow "which makes that function a template the compiler calls. A record")
			(reflow " ")
			(reflow "field and a list element have nothing to hold.")))
	(report
		(severity runtime_error)
		(title "Code Is Not Allowed Here")
		(region (start 4 18) (end 4 34))
		(headline
			(reflow "A Code can name a function's parameter, or what a function returns."))
		(document
			(source-region (file "staged_code_outside_staged_position.md") (start 4 18) (end 4 34) (annotation error) (line-text "nested : (Str -> Code(F32 -> F32)) -> Str"))
			(line-break)
			(reflow "A")
			(reflow " ")
			(annotated emphasis "Code")
			(reflow " ")
			(reflow "exists only while the compiler runs, so it names a function")
			(reflow " ")
			(reflow "parameter, which takes a description, or what a function returns,")
			(reflow " ")
			(reflow "which makes that function a template the compiler calls. A record")
			(reflow " ")
			(reflow "field and a list element have nothing to hold.")))
	(report
		(severity runtime_error)
		(title "Code Is Not Allowed Here")
		(region (start 7 15) (end 7 31))
		(headline
			(reflow "A Code can name a function's parameter, or what a function returns."))
		(document
			(source-region (file "staged_code_outside_staged_position.md") (start 7 15) (end 7 31) (annotation error) (line-text "lister : List(Code(F32 -> F32)) -> Str"))
			(line-break)
			(reflow "A")
			(reflow " ")
			(annotated emphasis "Code")
			(reflow " ")
			(reflow "exists only while the compiler runs, so it names a function")
			(reflow " ")
			(reflow "parameter, which takes a description, or what a function returns,")
			(reflow " ")
			(reflow "which makes that function a template the compiler calls. A record")
			(reflow " ")
			(reflow "field and a list element have nothing to hold."))))
~~~
# TOKENS
~~~zig
LowerIdent,OpColon,OpenCurly,LowerIdent,OpColon,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,CloseCurly,OpArrow,UpperIdent,
LowerIdent,OpAssign,OpBar,NamedUnderscore,OpBar,StringStart,StringPart,StringEnd,
LowerIdent,OpColon,OpenRound,UpperIdent,OpArrow,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,CloseRound,OpArrow,UpperIdent,
LowerIdent,OpAssign,OpBar,NamedUnderscore,OpBar,StringStart,StringPart,StringEnd,
LowerIdent,OpColon,UpperIdent,NoSpaceOpenRound,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,CloseRound,OpArrow,UpperIdent,
LowerIdent,OpAssign,OpBar,NamedUnderscore,OpBar,StringStart,StringPart,StringEnd,
LowerIdent,OpColon,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,OpArrow,UpperIdent,
LowerIdent,OpAssign,OpBar,NamedUnderscore,OpBar,StringStart,StringPart,StringEnd,
LowerIdent,OpColon,UpperIdent,OpArrow,UpperIdent,NoSpaceOpenRound,UpperIdent,OpArrow,UpperIdent,CloseRound,
LowerIdent,OpAssign,OpBar,LowerIdent,OpBar,OpBar,LowerIdent,OpBar,LowerIdent,OpStar,LowerIdent,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-type-anno (name "holder")
			(ty-fn
				(ty-record
					(anno-record-field (name "staged")
						(ty-apply
							(ty (name "Code"))
							(ty-fn
								(ty (name "F32"))
								(ty (name "F32"))))))
				(ty (name "Str"))))
		(s-decl
			(p-ident (raw "holder"))
			(e-lambda
				(args
					(p-ident (raw "_r")))
				(e-string
					(e-string-part (raw "x")))))
		(s-type-anno (name "nested")
			(ty-fn
				(ty-fn
					(ty (name "Str"))
					(ty-apply
						(ty (name "Code"))
						(ty-fn
							(ty (name "F32"))
							(ty (name "F32")))))
				(ty (name "Str"))))
		(s-decl
			(p-ident (raw "nested"))
			(e-lambda
				(args
					(p-ident (raw "_f")))
				(e-string
					(e-string-part (raw "x")))))
		(s-type-anno (name "lister")
			(ty-fn
				(ty-apply
					(ty (name "List"))
					(ty-apply
						(ty (name "Code"))
						(ty-fn
							(ty (name "F32"))
							(ty (name "F32")))))
				(ty (name "Str"))))
		(s-decl
			(p-ident (raw "lister"))
			(e-lambda
				(args
					(p-ident (raw "_l")))
				(e-string
					(e-string-part (raw "x")))))
		(s-type-anno (name "accepted")
			(ty-fn
				(ty-apply
					(ty (name "Code"))
					(ty-fn
						(ty (name "F32"))
						(ty (name "F32"))))
				(ty (name "Str"))))
		(s-decl
			(p-ident (raw "accepted"))
			(e-lambda
				(args
					(p-ident (raw "_c")))
				(e-string
					(e-string-part (raw "x")))))
		(s-type-anno (name "template")
			(ty-fn
				(ty (name "F32"))
				(ty-apply
					(ty (name "Code"))
					(ty-fn
						(ty (name "F32"))
						(ty (name "F32"))))))
		(s-decl
			(p-ident (raw "template"))
			(e-lambda
				(args
					(p-ident (raw "factor")))
				(e-lambda
					(args
						(p-ident (raw "x")))
					(e-binop (op "*")
						(e-ident (raw "x"))
						(e-ident (raw "factor"))))))))
~~~
# FORMATTED
~~~roc
NO CHANGE
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "holder"))
		(e-runtime-error (tag "erroneous_value_expr"))
		(annotation
			(ty-fn (effectful false)
				(ty-record
					(field (field "staged")
						(ty-apply (name "Code") (builtin)
							(ty-fn (effectful false)
								(ty-lookup (name "F32") (builtin))
								(ty-lookup (name "F32") (builtin))))))
				(ty-lookup (name "Str") (builtin)))))
	(d-let
		(p-assign (ident "nested"))
		(e-runtime-error (tag "erroneous_value_expr"))
		(annotation
			(ty-fn (effectful false)
				(ty-parens
					(ty-fn (effectful false)
						(ty-lookup (name "Str") (builtin))
						(ty-apply (name "Code") (builtin)
							(ty-fn (effectful false)
								(ty-lookup (name "F32") (builtin))
								(ty-lookup (name "F32") (builtin))))))
				(ty-lookup (name "Str") (builtin)))))
	(d-let
		(p-assign (ident "lister"))
		(e-runtime-error (tag "erroneous_value_expr"))
		(annotation
			(ty-fn (effectful false)
				(ty-apply (name "List") (builtin)
					(ty-apply (name "Code") (builtin)
						(ty-fn (effectful false)
							(ty-lookup (name "F32") (builtin))
							(ty-lookup (name "F32") (builtin)))))
				(ty-lookup (name "Str") (builtin)))))
	(d-let
		(p-assign (ident "accepted"))
		(e-lambda
			(args
				(p-assign (ident "_c")))
			(e-string
				(e-literal (string "x"))))
		(annotation
			(ty-fn (effectful false)
				(ty-apply (name "Code") (builtin)
					(ty-fn (effectful false)
						(ty-lookup (name "F32") (builtin))
						(ty-lookup (name "F32") (builtin))))
				(ty-lookup (name "Str") (builtin)))))
	(d-let
		(p-assign (ident "template"))
		(e-lambda
			(args
				(p-assign (ident "factor")))
			(e-closure
				(captures
					(capture (ident "factor")))
				(e-lambda
					(args
						(p-assign (ident "x")))
					(e-dispatch-call (method "times") (constraint-fn-var 547)
						(receiver
							(e-lookup-local
								(p-assign (ident "x"))))
						(args
							(e-lookup-local
								(p-assign (ident "factor"))))))))
		(annotation
			(ty-fn (effectful false)
				(ty-lookup (name "F32") (builtin))
				(ty-apply (name "Code") (builtin)
					(ty-fn (effectful false)
						(ty-lookup (name "F32") (builtin))
						(ty-lookup (name "F32") (builtin))))))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "{ staged: Error } -> Str"))
		(patt (type "(Str -> Error) -> Str"))
		(patt (type "List(Error) -> Str"))
		(patt (type "Code(F32 -> F32) -> Str"))
		(patt (type "F32 -> Code(F32 -> F32)")))
	(expressions
		(expr (type "{ staged: Error } -> Str"))
		(expr (type "(Str -> Error) -> Str"))
		(expr (type "List(Error) -> Str"))
		(expr (type "Code(F32 -> F32) -> Str"))
		(expr (type "F32 -> Code(F32 -> F32)"))))
~~~
