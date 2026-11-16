# roc-lang/roc#12720: the platform module `Bool` has the name of a builtin
# type, which is a reserved module name. Checking reports it, and the hosted
# entry `Bool.level!` that goes through it does not crash the compiler.
platform "p"
	requires { main! : () => {} }
	exposes [Bool]
	packages {}
	provides { "roc_main": main_for_host! }
	hosted { "roc_level": Bool.level! }
	targets: {}

import Bool

main_for_host! : () => {}
main_for_host! = main!
