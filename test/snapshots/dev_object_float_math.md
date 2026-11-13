# META
~~~ini
description=F32/F64 arithmetic, comparisons, and F64 to I64 conversion in host-called functions
type=dev_object
~~~
# SOURCE
## app.roc
~~~roc
app [main] { pf: platform "./platform.roc" }

main : F64, F32, I64 -> I64
main = |x, y, n| {
    scaled = x * 2.5 - I64.to_f64(n) / 3.0
    narrowed = F32.to_f64(y * 1.5 + 0.25)
    total = if scaled > narrowed { scaled - narrowed } else { narrowed + scaled }
    F64.to_i64_wrap(total)
}
~~~
## platform.roc
~~~roc
platform ""
    requires {} { main : F64, F32, I64 -> I64 }
    exposes []
    packages {}
    provides { "roc_main": main_for_host }
    targets: {
        inputs_dir: "targets/",
        x64glibc: { inputs: [app] },
    }

main_for_host : F64, F32, I64 -> I64
main_for_host = main
~~~
# MONO
~~~roc
# platform
main_for_host = <required>

# app
main = |x, y, n| {
	scaled = x * 2.5 - to_f64(n) / 3
	narrowed = to_f64(y * 1.5 + 0.25)
	total = if (scaled > narrowed) {
		scaled - narrowed
	} else {
		narrowed + scaled
	}
	to_i64_wrap(total)
}

~~~
# DEV OUTPUT
~~~ini
x64mac=d8b742d4caf870e2814f25207c73db5131eb013dc943dde585b3018670625dc8
x64win=56beb7b6cdd6525046db9e6c3959e8b71f42479629726b002f66979fadc889dc
x64mingw=56beb7b6cdd6525046db9e6c3959e8b71f42479629726b002f66979fadc889dc
x64freebsd=5a288a3f36fd0704d0174fb5403ee4b81fdd9b180e3a5b0c41f6c8b57e71d31d
x64openbsd=936fd51c26b33d708674a0662ce9b308c5cc3c27331cd0a2658d54327a5b412c
x64netbsd=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64musl=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64glibc=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64linux=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64elf=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64v1mac=d8b742d4caf870e2814f25207c73db5131eb013dc943dde585b3018670625dc8
x64v1win=56beb7b6cdd6525046db9e6c3959e8b71f42479629726b002f66979fadc889dc
x64v1mingw=56beb7b6cdd6525046db9e6c3959e8b71f42479629726b002f66979fadc889dc
x64v1freebsd=5a288a3f36fd0704d0174fb5403ee4b81fdd9b180e3a5b0c41f6c8b57e71d31d
x64v1openbsd=936fd51c26b33d708674a0662ce9b308c5cc3c27331cd0a2658d54327a5b412c
x64v1netbsd=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64v1musl=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64v1glibc=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64v1linux=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
x64v1elf=dc3cb25c520e6bde6091d3c8be48f2ca1274894f17d866adef19a9214275a810
arm64mac=365ca3c71d35f38ef1b2e0ee67d350127fa0c2156698999c06ed9faad329ac3b
arm64win=0d2dd8081a8564af74475ed2c0bbf3c3b4e54dbba7d0262e94608dc10287e982
arm64mingw=0d2dd8081a8564af74475ed2c0bbf3c3b4e54dbba7d0262e94608dc10287e982
arm64linux=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm64musl=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm64glibc=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm64v1win=0d2dd8081a8564af74475ed2c0bbf3c3b4e54dbba7d0262e94608dc10287e982
arm64v1mingw=0d2dd8081a8564af74475ed2c0bbf3c3b4e54dbba7d0262e94608dc10287e982
arm64v1linux=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm64v1musl=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm64v1glibc=45430889d5e17770ece649aa03018276903f1d692a610076786e161ed89663e7
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
