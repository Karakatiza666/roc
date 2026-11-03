# META
~~~ini
description=Formatter stability for open tag unions with blank lines before ..
type=snippet
~~~
# SOURCE
~~~roc
r : [
	a,

	..,
]
~~~
# EXPECTED
MALFORMED TYPE - open_tag_union_stability.md:2:2:2:3
# PROBLEMS
~~~clojure
(reports
	(report
		(severity runtime_error)
		(title "Malformed Type")
		(region (start 2 2) (end 2 3))
		(headline
			(reflow "This type annotation is malformed or contains invalid syntax."))
		(document
			(source-region (file "open_tag_union_stability.md") (start 2 2) (end 2 3) (annotation error) (line-text "\ta,")))))
~~~
# TOKENS
~~~zig
LowerIdent,OpColon,OpenSquare,
LowerIdent,Comma,
DoubleDot,Comma,
CloseSquare,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-type-anno (name "r")
			(ty-tag-union
				(tags
					(ty-var (raw "a")))
				..))))
~~~
# FORMATTED
~~~roc
NO CHANGE
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "r"))
		(e-runtime-error (tag "erroneous_value_expr"))
		(annotation
			(ty-tag-union
				(ty-malformed)
				(ty-rigid-var (name "#others"))))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Error")))
	(expressions
		(expr (type "Error"))))
~~~
