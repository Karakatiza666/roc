import Db

Other :: {}.{
	## An encoder that holds a Code site at its own variable `a`.
	encode = |encoding| |value, state| Json.encode_str(encoding, Db.of(value).filter(|_x| Bool.True).show(), state)
}
