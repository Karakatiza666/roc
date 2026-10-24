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
x64mac=c35e293ce524cacfb44a0cd0ce832b280f1dbe9af3a2fedd9a085132521ee6c7
x64win=9c761f4730a1867c46c6534ada692d4febfa21534259d55fc1815dedcb177a1d
x64mingw=9c761f4730a1867c46c6534ada692d4febfa21534259d55fc1815dedcb177a1d
x64freebsd=d0194050c8b754f72e311551768a70475222e7db58eefc50904aee723cae1c0e
x64openbsd=47b46b5c6054db4a097b7b9e4cec004f6b97a27d26db6ca8dbdae93d0edc53a9
x64netbsd=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64musl=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64glibc=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64linux=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64elf=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64v1mac=c35e293ce524cacfb44a0cd0ce832b280f1dbe9af3a2fedd9a085132521ee6c7
x64v1win=9c761f4730a1867c46c6534ada692d4febfa21534259d55fc1815dedcb177a1d
x64v1mingw=9c761f4730a1867c46c6534ada692d4febfa21534259d55fc1815dedcb177a1d
x64v1freebsd=d0194050c8b754f72e311551768a70475222e7db58eefc50904aee723cae1c0e
x64v1openbsd=47b46b5c6054db4a097b7b9e4cec004f6b97a27d26db6ca8dbdae93d0edc53a9
x64v1netbsd=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64v1musl=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64v1glibc=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64v1linux=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
x64v1elf=1a4ef9af79f6c6897cfe34367d83eccc1d2ef0522bf917ee4b5921c1f7f8ef1a
arm64mac=84f50dd49391a236b8b637be4c51642cf1e94db99f4b476d09f3d34507189468
arm64win=7dde5c3ae1a3b5123d86acb779fcda4976e87e0067e9b0da06db2b9492ec9735
arm64mingw=7dde5c3ae1a3b5123d86acb779fcda4976e87e0067e9b0da06db2b9492ec9735
arm64linux=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm64musl=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm64glibc=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm64v1win=7dde5c3ae1a3b5123d86acb779fcda4976e87e0067e9b0da06db2b9492ec9735
arm64v1mingw=7dde5c3ae1a3b5123d86acb779fcda4976e87e0067e9b0da06db2b9492ec9735
arm64v1linux=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm64v1musl=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm64v1glibc=dd7090166e2ce776fd1f3ed45c0a404e5acd3653c30aaec96b285efd35540f5f
arm32linux=NOT_IMPLEMENTED
arm32musl=NOT_IMPLEMENTED
wasm32=NOT_IMPLEMENTED
wasm32v1=NOT_IMPLEMENTED
~~~
