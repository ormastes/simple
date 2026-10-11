# Item 5 current-source Stage 2 hello loader attribution — 2026-10-11

Status: diagnostic only. This is an admitted Stage 2 native-build, not a Stage 4 release-small image or a BS7 size/startup cohort.

## Provenance

- Branch: `work/targets-release-20261010` at `61c1e0c579e`.
- Fixture: `test/05_perf/startup/hello_fixture.spl`, SHA-256 `b80792336156c7b0f7fe02eeef24610d2d52a10d1810397744471d1dc5738180`.
- Compiler: admitted pure-Simple Stage 2 SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`.
- Build: `SIMPLE_LIB=src SIMPLE_LINKER=lld SIMPLE_NO_STUB_FALLBACK=1 <compiler> native-build --source test/05_perf/startup --entry-closure --entry test/05_perf/startup/hello_fixture.spl --runtime-bundle core-c-bootstrap --backend cranelift --output build/item5-hello-attribution`.
- LLD SHA-256: `3b2e366d1a5bcdd2e305a6f4997e809e8af2c46b84469c1a6b496337591a1833`. LLVM strip SHA-256: `53aa959cdd1eb9e011f09de021064df4e824d666f01a013ef5cae83808d34e81`.
- Unstripped binary: 16,704 bytes, SHA-256 `b260a861a65bca1d0d5f4680aac879df99cd14a0e6a1aba49642e872a22b1743`.
- A copy stripped with `llvm-strip --strip-all`: 9,800 bytes, SHA-256 `a623d681d60691fb8f17d1702c2d203fe1763bf3154cf42da7531953dcc7d38b`. This ad hoc strip is not the selected release-small link/strip contract.

## Observations

The binary exits 0 and prints exactly `hello\n`. `readelf -d` lists only `libc.so.6` and `ld-linux-aarch64.so.1` as needed libraries; no optional provider is a direct dynamic dependency. `nm` lists no `mmap` or `munmap` reference. It does retain `simple_startup_load_aspect_pack`, `dlopen`, `dlsym`, `dlclose`, and `prof_sample_init`. With `SIMPLE_STARTUP_ASPECTS` empty and `--startup-extension=/tmp/simple-missing-aspect-pack-item5.so`, startup exits 125 before the application and names the missing pack.

The native-build command also warns that default dynload mode produced no automatic aspect pack. The profiler constructor is retained by the bootstrap linker’s `prof_sample_force_link` root; that is stage-scoped and does not prove the pure-Simple Stage 4 linker retains it. A zero-import hello does not call Simple-owned mmap, so removing mmap is not the next size cut for this fixture. The next implementation boundary is admitted aspect-pack production and the exact startup/runtime retention contract, followed by matched Stage 4 size, startup, and RSS cohorts.
