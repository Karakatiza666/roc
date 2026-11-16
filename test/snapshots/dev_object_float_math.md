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
x64mac=ca1e2f6846786105648e2a834f547844a8e7905bd77331d701f8569d1cf8faf3
x64win=fc99f8976ad295e5319453786344d3458bf4491e32634232b311941d83b00863
x64mingw=fc99f8976ad295e5319453786344d3458bf4491e32634232b311941d83b00863
x64freebsd=d58befb7ba0e9ca1c6d692f0a9a2272dce6f1662f05e2c7cd3f762262fec5969
x64openbsd=c0b8a400d51ff859169ddd290fd6be1d765e1a8e8b1d15834ec6b5daac8cc1ff
x64netbsd=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64musl=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64glibc=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64linux=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64elf=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64v1mac=ca1e2f6846786105648e2a834f547844a8e7905bd77331d701f8569d1cf8faf3
x64v1win=fc99f8976ad295e5319453786344d3458bf4491e32634232b311941d83b00863
x64v1mingw=fc99f8976ad295e5319453786344d3458bf4491e32634232b311941d83b00863
x64v1freebsd=d58befb7ba0e9ca1c6d692f0a9a2272dce6f1662f05e2c7cd3f762262fec5969
x64v1openbsd=c0b8a400d51ff859169ddd290fd6be1d765e1a8e8b1d15834ec6b5daac8cc1ff
x64v1netbsd=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64v1musl=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64v1glibc=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64v1linux=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
x64v1elf=4415cc81d67f397f28bee3b347ceef56e692ab50ea2886d694c86efe870984b0
arm64mac=5941415d082174ceeeda1e703e28dc59af741af2aff7b66036a1a78c8e1dfdeb
arm64win=c2fe3899284799b9bf74097a6c42daac3f7ab1affb3c7dba8c4f0b4487884432
arm64mingw=c2fe3899284799b9bf74097a6c42daac3f7ab1affb3c7dba8c4f0b4487884432
arm64linux=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm64musl=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm64glibc=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm64v1win=c2fe3899284799b9bf74097a6c42daac3f7ab1affb3c7dba8c4f0b4487884432
arm64v1mingw=c2fe3899284799b9bf74097a6c42daac3f7ab1affb3c7dba8c4f0b4487884432
arm64v1linux=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm64v1musl=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm64v1glibc=6d12b96c435597c7793c10715b4feebe234273fe747726c5a980911e435965fb
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
