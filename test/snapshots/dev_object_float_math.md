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
x64mac=c1757e74a0d65f97e35d05e11f861ca4c7e05c111052da732aed3fce3d05355e
x64win=6d8a7526040d0f90ab3f1065a5c4426879f01e515f1bf38a8de15ecde55c7d9d
x64mingw=6d8a7526040d0f90ab3f1065a5c4426879f01e515f1bf38a8de15ecde55c7d9d
x64freebsd=93fe49719b93e0d31b2728f9371dc76f443081ad80878ceacd029f97815b69d6
x64openbsd=064644e218796feec28bd4503598156d2fbffcec5e9fe6b33b2140d7f169727f
x64netbsd=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64musl=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64glibc=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64linux=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64elf=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64v1mac=c1757e74a0d65f97e35d05e11f861ca4c7e05c111052da732aed3fce3d05355e
x64v1win=6d8a7526040d0f90ab3f1065a5c4426879f01e515f1bf38a8de15ecde55c7d9d
x64v1mingw=6d8a7526040d0f90ab3f1065a5c4426879f01e515f1bf38a8de15ecde55c7d9d
x64v1freebsd=93fe49719b93e0d31b2728f9371dc76f443081ad80878ceacd029f97815b69d6
x64v1openbsd=064644e218796feec28bd4503598156d2fbffcec5e9fe6b33b2140d7f169727f
x64v1netbsd=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64v1musl=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64v1glibc=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64v1linux=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
x64v1elf=6592ebe76eb280b1b5b5034c0c8fecf5c7fca6b7dbccecb1197b655c582141eb
arm64mac=3e32194dd2e772f46f752aac8d840c28151eb459a2349872bb7aa6e46e571490
arm64win=db9c649cd3be1317a643b4028f3c6510872a28fb92f1b51d3806254dc074db3f
arm64mingw=db9c649cd3be1317a643b4028f3c6510872a28fb92f1b51d3806254dc074db3f
arm64linux=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm64musl=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm64glibc=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm64v1win=db9c649cd3be1317a643b4028f3c6510872a28fb92f1b51d3806254dc074db3f
arm64v1mingw=db9c649cd3be1317a643b4028f3c6510872a28fb92f1b51d3806254dc074db3f
arm64v1linux=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm64v1musl=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm64v1glibc=439f3691996b0139360789f3def0dab14ca6b9ec65923ca6ff630d34e9c13abb
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
