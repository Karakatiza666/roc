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
x64mac=8de4cc0583861652365cb24cb8131daf3ebba3d2fdbfc14df9d36e20452aa9d4
x64win=1f5f55dd3f998b81997558ab74c62f4e9e0954636f96991fd77e6de52d066d97
x64mingw=1f5f55dd3f998b81997558ab74c62f4e9e0954636f96991fd77e6de52d066d97
x64freebsd=b675769da54efb9982bda73c63f1b36ee187b99f30cc9c33ae2dd9908dbdf4b8
x64openbsd=6f00c2ddc9b7d725bed6f10b7c70bd610979c5797be003b8ca8668660022acd2
x64netbsd=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64musl=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64glibc=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64linux=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64elf=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64v1mac=8de4cc0583861652365cb24cb8131daf3ebba3d2fdbfc14df9d36e20452aa9d4
x64v1win=1f5f55dd3f998b81997558ab74c62f4e9e0954636f96991fd77e6de52d066d97
x64v1mingw=1f5f55dd3f998b81997558ab74c62f4e9e0954636f96991fd77e6de52d066d97
x64v1freebsd=b675769da54efb9982bda73c63f1b36ee187b99f30cc9c33ae2dd9908dbdf4b8
x64v1openbsd=6f00c2ddc9b7d725bed6f10b7c70bd610979c5797be003b8ca8668660022acd2
x64v1netbsd=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64v1musl=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64v1glibc=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64v1linux=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
x64v1elf=0a670fa47f250053a0085ed51784941ae5a58afc42398d37e7cdde9973d0084a
arm64mac=df6292ec91f5efdb965c1937e79befb0cc1da8cfee29c98b7e7d1c52c041fed5
arm64win=5ea7966c68dd63d47a0916c5ed3f654fceb786e6bb84b97f055a0384bebf239c
arm64mingw=5ea7966c68dd63d47a0916c5ed3f654fceb786e6bb84b97f055a0384bebf239c
arm64linux=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm64musl=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm64glibc=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm64v1win=5ea7966c68dd63d47a0916c5ed3f654fceb786e6bb84b97f055a0384bebf239c
arm64v1mingw=5ea7966c68dd63d47a0916c5ed3f654fceb786e6bb84b97f055a0384bebf239c
arm64v1linux=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm64v1musl=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm64v1glibc=01d386ff29836d432a55e7866575f5bc81f4f094586e99aa58aad563e46b3ef3
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
