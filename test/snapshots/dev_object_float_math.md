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
x64mac=fdde246a5d0959504eab9a7390b31a78e85a897cb5d15c5d133ef5c3d2fc16d6
x64win=b2d8d0da0345c6af6a8acfa3a1c97bf4a440b5261fa664238ccd908469b45f4b
x64mingw=b2d8d0da0345c6af6a8acfa3a1c97bf4a440b5261fa664238ccd908469b45f4b
x64freebsd=f57f6c051212484a4135155e9aee944292f9263e354919819961c9c815f20d96
x64openbsd=e5ed4803ef664f5d2c2d65edb2f322c933cf857bde161672549c2583f6a4d7e4
x64netbsd=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64musl=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64glibc=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64linux=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64elf=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64v1mac=fdde246a5d0959504eab9a7390b31a78e85a897cb5d15c5d133ef5c3d2fc16d6
x64v1win=b2d8d0da0345c6af6a8acfa3a1c97bf4a440b5261fa664238ccd908469b45f4b
x64v1mingw=b2d8d0da0345c6af6a8acfa3a1c97bf4a440b5261fa664238ccd908469b45f4b
x64v1freebsd=f57f6c051212484a4135155e9aee944292f9263e354919819961c9c815f20d96
x64v1openbsd=e5ed4803ef664f5d2c2d65edb2f322c933cf857bde161672549c2583f6a4d7e4
x64v1netbsd=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64v1musl=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64v1glibc=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64v1linux=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
x64v1elf=b08a4e758c5d6e5e93730a46b5b4ea777dbd68a10f402728d7f06c4a7844636b
arm64mac=0f22d8095cea45f6424bb7a6c3b0fe7bfbbaa82e0a665e3538cf63d388a39e14
arm64win=d45396888f131202185018a41b452452f800c917932b085101382501f3ea17ce
arm64mingw=d45396888f131202185018a41b452452f800c917932b085101382501f3ea17ce
arm64linux=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm64musl=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm64glibc=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm64v1win=d45396888f131202185018a41b452452f800c917932b085101382501f3ea17ce
arm64v1mingw=d45396888f131202185018a41b452452f800c917932b085101382501f3ea17ce
arm64v1linux=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm64v1musl=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm64v1glibc=fcbb62340e0ed0df0883858e0e8bb578c08dc0b168c17e80753e8c794b3ace86
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
