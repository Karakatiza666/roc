# META
~~~ini
description=Method forward-references an anno-only sibling within the same associated block
type=file:Foo.roc
~~~
# SOURCE
~~~roc
Foo := [Whatever].{
    callMe : Foo
    callMe = absent

    absent : Foo
}
~~~
# EXPECTED
NAME NOT IN SCOPE - canon_revamp_forward_ref_to_anno_only.md:3:14:3:20
# PROBLEMS
~~~clojure
(reports
	(report
		(severity runtime_error)
		(title "Name Not In Scope")
		(region (start 3 14) (end 3 20))
		(headline
			(reflow "Nothing is named ")
			(annotated symbol-unqualified "absent")
			(reflow " in this scope."))
		(document
			(reflow "Is it misspelled, or is there an import missing?")
			(line-break)
			(line-break)
			(source-region (file "canon_revamp_forward_ref_to_anno_only.md") (start 3 14) (end 3 20) (annotation error) (line-text "    callMe = absent")))))
~~~
# TOKENS
~~~zig
UpperIdent,OpColonEqual,OpenSquare,UpperIdent,CloseSquare,Dot,OpenCurly,
LowerIdent,OpColon,UpperIdent,
LowerIdent,OpAssign,LowerIdent,
LowerIdent,OpColon,UpperIdent,
CloseCurly,
EndOfFile,
~~~
# PARSE
~~~clojure
(file
	(type-mod)
	(statements
		(s-type-decl
			(header (name "Foo")
				(args))
			(ty-tag-union
				(tags
					(ty (name "Whatever"))))
			(associated
				(s-type-anno (name "callMe")
					(ty (name "Foo")))
				(s-decl
					(p-ident (raw "callMe"))
					(e-ident (raw "absent")))
				(s-type-anno (name "absent")
					(ty (name "Foo")))))))
~~~
# FORMATTED
~~~roc
Foo := [Whatever].{
	callMe : Foo
	callMe = absent

	absent : Foo
}
~~~
# CANONICALIZE
~~~clojure
(can-ir
	(d-let
		(p-assign (ident "Foo.callMe"))
		(e-runtime-error (tag "ident_not_in_scope"))
		(annotation
			(ty-lookup (name "Foo") (local))))
	(d-let
		(p-assign (ident "Foo.absent"))
		(e-anno-only (kind "intrinsic"))
		(annotation
			(ty-lookup (name "Foo") (local))))
	(s-nominal-decl
		(ty-header (name "Foo"))
		(ty-tag-union
			(ty-tag-name (name "Whatever")))))
~~~
# TYPES
~~~clojure
(inferred-types
	(defs
		(patt (type "Foo"))
		(patt (type "Foo")))
	(type_decls
		(nominal (type "Foo")
			(ty-header (name "Foo"))))
	(expressions
		(expr (type "Foo"))
		(expr (type "Foo"))))
~~~
