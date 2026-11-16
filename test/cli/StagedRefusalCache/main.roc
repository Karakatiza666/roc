# The refused site is in an imported module. A module whose evaluation
# reports a refusal is never cached, so `roc check` reports it again with a
# warm cache.
import Lib

main! = |_args| {
	echo!("${Lib.staged}\n")
	Ok({})
}
