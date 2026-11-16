## A table handle that keeps its row type, read from an identity lambda.
T :: {}.{
	Table(row) := { name : Str, row_ty : Code.Ty }.{
		key : Table(row), Str -> Str
		key = |Table.(t), k| "${t.name}:${k}"
	}

	table : Str, Code(row -> row) -> Table(row)
	table = |name, code| Table.({ name: name, row_ty: code.graph().root_row().result })

	## A handle with no `Code` in it, for the control.
	Plain(row) := { name : Str }.{
		key : Plain(row), Str -> Str
		key = |Plain.(t), k| "${t.name}:${k}"
	}

	plain : Str -> Plain(row)
	plain = |name| Plain.({ name: name })
}
