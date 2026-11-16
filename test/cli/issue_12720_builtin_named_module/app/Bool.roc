Bool := [Yes, No].{
	not = |s| "user not ${s}"
	level = |s| "user level ${s}"
	show : Bool -> Str
	show = |b| match b {
		Bool.Yes => "yes"
		Bool.No => "no"
	}
}
