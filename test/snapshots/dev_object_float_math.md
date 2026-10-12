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
x64mac=b3a1bb4ebc32a78c8d39bab55384c50d66e46d5393cc1b6a7b419bc4d6e5a5fc
x64win=b795634fb15a6777bfa3c4d1d4ccc25bcc4a3818305b6d15db08a6496ffc3d24
x64mingw=b795634fb15a6777bfa3c4d1d4ccc25bcc4a3818305b6d15db08a6496ffc3d24
x64freebsd=a71e7d3860ff52a1d512d2ec410ebbcc008971e0f0bc22e8288495cb73f621cf
x64openbsd=a23ef547a441c96e07552db0f7c6df76b48257949424eefea129b8652cec4b6b
x64netbsd=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64musl=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64glibc=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64linux=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64elf=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64v1mac=b3a1bb4ebc32a78c8d39bab55384c50d66e46d5393cc1b6a7b419bc4d6e5a5fc
x64v1win=b795634fb15a6777bfa3c4d1d4ccc25bcc4a3818305b6d15db08a6496ffc3d24
x64v1mingw=b795634fb15a6777bfa3c4d1d4ccc25bcc4a3818305b6d15db08a6496ffc3d24
x64v1freebsd=a71e7d3860ff52a1d512d2ec410ebbcc008971e0f0bc22e8288495cb73f621cf
x64v1openbsd=a23ef547a441c96e07552db0f7c6df76b48257949424eefea129b8652cec4b6b
x64v1netbsd=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64v1musl=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64v1glibc=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64v1linux=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
x64v1elf=58db8430ba4717a9fcc0f392406d46154ce863797e322b30ae79f4c84b34b0bd
arm64mac=770685239b8e121bf2a57badf3afb569960ef190f51e737ddbdf267580e63eca
arm64win=396a6812aa8ab69e44f4b73bef4b36f489aaa2967020d9192ca0059671f030f4
arm64mingw=396a6812aa8ab69e44f4b73bef4b36f489aaa2967020d9192ca0059671f030f4
arm64linux=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm64musl=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm64glibc=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm64v1win=396a6812aa8ab69e44f4b73bef4b36f489aaa2967020d9192ca0059671f030f4
arm64v1mingw=396a6812aa8ab69e44f4b73bef4b36f489aaa2967020d9192ca0059671f030f4
arm64v1linux=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm64v1musl=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm64v1glibc=40ab8499e46e9028cdf20aa7d2d50463e9b8c214846fccdcdf49988dc91fb388
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
