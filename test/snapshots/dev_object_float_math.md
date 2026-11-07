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
x64mac=6234eb0a55f5811ce8893cfad150653bc2556b3df0715775726a90d223969ade
x64win=d1014d5c4eda4e678a557a662cfe234d4a209214efee0bd9c75340a64b2248dd
x64mingw=d1014d5c4eda4e678a557a662cfe234d4a209214efee0bd9c75340a64b2248dd
x64freebsd=4ccbca61d4f8142989ded9f0841eb9f8ffc3c3f990c3a143458af5182aef30ad
x64openbsd=b542efb87094cd2d6bf527e906c011a377118308f4088308727c0956863657ea
x64netbsd=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64musl=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64glibc=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64linux=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64elf=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64v1mac=6234eb0a55f5811ce8893cfad150653bc2556b3df0715775726a90d223969ade
x64v1win=d1014d5c4eda4e678a557a662cfe234d4a209214efee0bd9c75340a64b2248dd
x64v1mingw=d1014d5c4eda4e678a557a662cfe234d4a209214efee0bd9c75340a64b2248dd
x64v1freebsd=4ccbca61d4f8142989ded9f0841eb9f8ffc3c3f990c3a143458af5182aef30ad
x64v1openbsd=b542efb87094cd2d6bf527e906c011a377118308f4088308727c0956863657ea
x64v1netbsd=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64v1musl=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64v1glibc=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64v1linux=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
x64v1elf=cccbb4e54f854305b5519108ab4d57cba7d096e067b0ea3782f13033df06d347
arm64mac=8b8aa9ee88f168ca821de66fa0babf689c111dec96d7aa451ca813d7dc509760
arm64win=fe33d3af60442d89736417b6984a8e697fb14851aafa206a89f8e0f457b62c70
arm64mingw=fe33d3af60442d89736417b6984a8e697fb14851aafa206a89f8e0f457b62c70
arm64linux=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm64musl=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm64glibc=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm64v1win=fe33d3af60442d89736417b6984a8e697fb14851aafa206a89f8e0f457b62c70
arm64v1mingw=fe33d3af60442d89736417b6984a8e697fb14851aafa206a89f8e0f457b62c70
arm64v1linux=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm64v1musl=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm64v1glibc=b9f67a0f83165aa0bbd9451b6bc774832dddb3c7e157aef018b37a85c5a5c5fd
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
