# META
~~~ini
description=inline_ingested_file
type=snippet
~~~
# SOURCE
~~~roc
import "users.json" as data : Str
import Json

foo = Json.parse(data)
~~~
# EXPECTED
BUILTIN TYPE SHADOWED - inline_ingested_file.md:2:1:2:12
FILE NOT FOUND - inline_ingested_file.md:1:1:1:34
MOD NOT FOUND - inline_ingested_file.md:2:1:2:12
DOES NOT EXIST - inline_ingested_file.md:4:7:4:17
# PROBLEMS
~~~clojure
(reports
	(report
		(severity warning)
		(title "Builtin Type Shadowed")
		(region (start 2 1) (end 2 12))
		(headline
			(text "The type ")
			(annotated symbol-unqualified "Json")
			(text " shadows a builtin type."))
		(document
			(reflow "This may make the builtin type inaccessible in this scope.")
			(line-break)
			(source-region (file "inline_ingested_file.md") (start 2 1) (end 2 12) (annotation warning) (line-text "import Json"))))
	(report
		(severity runtime_error)
		(title "File Not Found")
		(region (start 1 1) (end 1 34))
		(headline
			(reflow "The file ")
			(annotated mod "users.json")
			(reflow " was not found."))
		(document
			(reflow "Make sure the file exists relative to your source file.")
			(line-break)
			(source-region (file "inline_ingested_file.md") (start 1 1) (end 1 34) (annotation error) (line-text "import \"users.json\" as data : Str"))))
	(report
		(severity runtime_error)
		(title "Mod Not Found")
		(region (start 2 1) (end 2 12))
		(headline
			(text "The mod ")
			(annotated code "Json")
			(reflow " was not found in this Roc project."))
		(document
			(source-region (file "inline_ingested_file.md") (start 2 1) (end 2 12) (annotation error) (line-text "import Json"))))
	(report
		(severity runtime_error)
		(title "Does Not Exist")
		(region (start 4 7) (end 4 17))
		(headline
			(annotated symbol-unqualified "Json.parse")
			(reflow " does not exist."))
		(document
			(source-region (file "inline_ingested_file.md") (start 4 7) (end 4 17) (annotation error) (line-text "foo = Json.parse(data)")))))
~~~
# TOKENS
~~~zig
KwImport,StringStart,StringPart,StringEnd,KwAs,LowerIdent,OpColon,UpperIdent,
KwImport,UpperIdent,
LowerIdent,OpAssign,UpperIdent,NoSpaceDotLowerIdent,NoSpaceOpenRound,LowerIdent,CloseRound,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-file-import
			(path "users.json")
			(name "data")
			(type "Str"))
		(s-import (raw "Json"))
		(s-decl
			(p-ident (raw "foo"))
			(e-apply
				(e-ident (raw "Json.parse"))
				(e-ident (raw "data"))))))
~~~
# FORMATTED
~~~roc
NO CHANGE
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "data"))
		(e-runtime-error (tag "file_import_not_found")))
	(d-let
		(p-assign (ident "foo"))
		(e-runtime-error (tag "erroneous_value_expr")))
	(s-import (mod "Json") (alias "Json")
		(exposes)))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Error"))
		(patt (type "Error")))
	(expressions
		(expr (type "Error"))
		(expr (type "Error"))))
~~~
