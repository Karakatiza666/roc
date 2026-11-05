# META
~~~ini
description=Exposed item name conflicts with local definitions
type=snippet
~~~
# SOURCE
~~~roc
import json.Json exposing [parse]

# Local definition with same name as exposed item
parse = 42

main = {
    result = parse
    result
}
~~~
# EXPECTED
BUILTIN TYPE SHADOWED - can_import_exposing_conflicts.md:1:1:1:34
# PROBLEMS
~~~clojure
(reports
	(report
		(severity warning)
		(title "Builtin Type Shadowed")
		(region (start 1 1) (end 1 34))
		(headline
			(text "The type ")
			(annotated symbol-unqualified "Json")
			(text " shadows a builtin type."))
		(document
			(reflow "This may make the builtin type inaccessible in this scope.")
			(line-break)
			(source-region (file "can_import_exposing_conflicts.md") (start 1 1) (end 1 34) (annotation warning) (line-text "import json.Json exposing [parse]")))))
~~~
# TOKENS
~~~zig
KwImport,LowerIdent,NoSpaceDotUpperIdent,KwExposing,OpenSquare,LowerIdent,CloseSquare,
LowerIdent,OpAssign,Int,
LowerIdent,OpAssign,OpenCurly,
LowerIdent,OpAssign,LowerIdent,
LowerIdent,
CloseCurly,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-import (raw "json.Json")
			(exposing
				(exposed-lower-ident
					(text "parse"))))
		(s-decl
			(p-ident (raw "parse"))
			(e-int (raw "42")))
		(s-decl
			(p-ident (raw "main"))
			(e-block
				(statements
					(s-decl
						(p-ident (raw "result"))
						(e-ident (raw "parse")))
					(e-ident (raw "result")))))))
~~~
# FORMATTED
~~~roc
import json.Json exposing [parse]

# Local definition with same name as exposed item
parse = 42

main = {
	result = parse
	result
}
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "parse"))
		(e-num (value "42")))
	(d-let
		(p-assign (ident "main"))
		(e-block
			(s-let
				(p-assign (ident "result"))
				(e-lookup-local
					(p-assign (ident "parse"))))
			(e-lookup-local
				(p-assign (ident "result")))))
	(s-import (mod "json.Json") (alias "Json")
		(exposes
			(exposed (name "parse") (wildcard false)))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Dec"))
		(patt (type "Dec")))
	(expressions
		(expr (type "Dec"))
		(expr (type "Dec"))))
~~~
