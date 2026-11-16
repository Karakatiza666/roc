module [Bool, Encoding]

Bool := [Yes, No, True].{
	show : Bool -> Str
	show = |b| match b {
		Yes => "foo yes"
		No => "foo no"
		True => "foo true"
	}
}

Encoding := [Plain, Fancy].{
	name : Encoding -> Str
	name = |e| match e {
		Plain => "plain"
		Fancy => "fancy"
	}
}
