# META
~~~ini
description=Import with mod-qualified usage
type=snippet
~~~
# SOURCE
~~~roc
import json.Json

main = Json.utf8
~~~
# EXPECTED
BUILTIN TYPE SHADOWED - can_import_json.md:1:1:1:17
DOES NOT EXIST - can_import_json.md:3:8:3:17
# PROBLEMS
~~~clojure
(reports
	(report
		(severity warning)
		(title "Builtin Type Shadowed")
		(region (start 1 1) (end 1 17))
		(headline
			(text "The type ")
			(annotated symbol-unqualified "Json")
			(text " shadows a builtin type."))
		(document
			(reflow "This may make the builtin type inaccessible in this scope.")
			(line-break)
			(source-region (file "can_import_json.md") (start 1 1) (end 1 17) (annotation warning) (line-text "import json.Json"))))
	(report
		(severity runtime_error)
		(title "Does Not Exist")
		(region (start 3 8) (end 3 17))
		(headline
			(annotated symbol-unqualified "Json.utf8")
			(reflow " does not exist."))
		(document
			(source-region (file "can_import_json.md") (start 3 8) (end 3 17) (annotation error) (line-text "main = Json.utf8")))))
~~~
# TOKENS
~~~zig
KwImport,LowerIdent,NoSpaceDotUpperIdent,
LowerIdent,OpAssign,UpperIdent,NoSpaceDotLowerIdent,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-import (raw "json.Json"))
		(s-decl
			(p-ident (raw "main"))
			(e-ident (raw "Json.utf8")))))
~~~
# FORMATTED
~~~roc
NO CHANGE
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "main"))
		(e-runtime-error (tag "qualified_ident_does_not_exist")))
	(s-import (mod "json.Json")
		(exposes)))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Error")))
	(expressions
		(expr (type "Error"))))
~~~
