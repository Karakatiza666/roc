# roc-lang/roc#12720: the platform module `Bool` has the name of a builtin
# type. `import Bool` names this module, so the hosted entry `Bool.level!`
# resolves to its `level!`, not to a member of the builtin `Bool`.
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
