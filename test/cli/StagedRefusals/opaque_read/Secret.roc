Secret :: { code : U16 }.{
	make : U16 -> Secret
	make = |code| Secret.({ code: code })
}
