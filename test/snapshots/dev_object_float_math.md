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
x64mac=783cd6064d74f35ae4865934772555670b6f3ceef20dc649dbba0246a6b7fa1d
x64win=f7f1d0dee429ac3a9e6c08febc1db12a00ed5d4de9c13c9ef9b41a709208d070
x64mingw=f7f1d0dee429ac3a9e6c08febc1db12a00ed5d4de9c13c9ef9b41a709208d070
x64freebsd=0c80e020cf9084a3d9bddc856ddeb7b7d6119c5dddc702ee435c33c2888bf142
x64openbsd=18a494acf5b0e6ca457c7e933cfa24a7c1dcc13742c56a904b63952529cb81f5
x64netbsd=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64musl=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64glibc=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64linux=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64elf=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64v1mac=783cd6064d74f35ae4865934772555670b6f3ceef20dc649dbba0246a6b7fa1d
x64v1win=f7f1d0dee429ac3a9e6c08febc1db12a00ed5d4de9c13c9ef9b41a709208d070
x64v1mingw=f7f1d0dee429ac3a9e6c08febc1db12a00ed5d4de9c13c9ef9b41a709208d070
x64v1freebsd=0c80e020cf9084a3d9bddc856ddeb7b7d6119c5dddc702ee435c33c2888bf142
x64v1openbsd=18a494acf5b0e6ca457c7e933cfa24a7c1dcc13742c56a904b63952529cb81f5
x64v1netbsd=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64v1musl=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64v1glibc=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64v1linux=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
x64v1elf=37b5d9837685743845fdc845f63acbc3262df8b2f0272492000a54912543081e
arm64mac=4a7c7d8af70d32d4a4324fdff704110a55418234b56949493a1796e14eef4cad
arm64win=f91b93058c50a06310374082df10c5353c37a5bce720d7c8a7c6a21f4b58772f
arm64mingw=f91b93058c50a06310374082df10c5353c37a5bce720d7c8a7c6a21f4b58772f
arm64linux=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm64musl=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm64glibc=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm64v1win=f91b93058c50a06310374082df10c5353c37a5bce720d7c8a7c6a21f4b58772f
arm64v1mingw=f91b93058c50a06310374082df10c5353c37a5bce720d7c8a7c6a21f4b58772f
arm64v1linux=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm64v1musl=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm64v1glibc=d9429a24959b6526c8732762afc36ca2d3a01f111a12b27c2221a3d765119075
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
