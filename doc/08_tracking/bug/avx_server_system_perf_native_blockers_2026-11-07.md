# AVX server system perf: native build blockers with the admitted Windows Stage 2

Status: OPEN (items 1-6 fixed, see Progress). Found 2026-11-07 on DESKTOP-5A4V03J (Xeon W-2135, AVX-512, MinGW
clang lane, `--backend=cranelift`).

Compiler: admitted Stage 2 from release `060ecf462c5`
(`stage2-admitted/simple.exe` sha256 `4a2a5d2d67425b962731ba97bda607de2c03ce06b50ec34657e67e349908e981`,
sanity `status=pass`). Source: release `58c590c6120`. Runner:
`scripts/check/check-avx-server-system-perf.shs` (MODE=native), levelled
provider DLLs rebuilt from that source (`check-vector-provider-levels.shs run`:
PASS 40/40, L4 bitmap AND 3.3x / HTTP CRLF 28.5x vs scalar).
Env: `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, `SIMPLE_{HIR,MIR}_SHARD_WORKER_KB=3000000`,
`SIMPLE_BUILD_MEMORY_RESERVE_BYTES=10 GiB` (as the Windows sanity probes use).

Verdict: `FAIL — 3 checked, 3 failed` (web_server, db_server, loadgen did not build).

## 1. Trait-object to trait-object assignment demands an impl for an empty type (web server, on the AVX path)

`src/lib/nogc_sync_mut/http_server/server.spl:303`
`self.request_parser = parsed.parser` (both `HttpRequestParserV1?`) fails native
MIR lowering with
`missing native trait implementation: lib.nogc_sync_mut.http_server.request_parser::HttpRequestParserV1 for  at ...server.spl:303:17`.
The value is already a trait object; the assignment must not look for a
concrete impl. This is the only error on the sync `SimpleHttpServer` path the
HTTP vector parser uses.

## 2. Trait-object method call unresolved (DB server, on the AVX path)

`unresolved method call: close_owned_v1 route=runtime-fallback key=PureDatabaseBitmapReducerV1::close_owned_v1 owner=PureDatabaseBitmapReducerV1 struct_method_syms=no`
— the only error in the `postgres_mimic_server` closure. Calling a trait method
on a trait-typed value (`PureDatabaseBitmapReducerV1`, the bitmap reducer slot)
does not dispatch natively. Same family as item 1.

## 3. Windows link fails with the error text swallowed (loadgen)

`test/03_system/tools/avx_server_loadgen.spl`: all 72 modules compile (111
objects), then `[LINKER] os=windows` → `link_to_native returned` →
`failed link inputs retained for replay`, exit 1, and **no error text and no
link-command sidecar** (`record_link_command` is never reached, so the failure
is inside `link_native_windows_with_engine` before a linker runs). Also seen on a
hand-built `p2_add` diagnostic outside the gate; the gate's own `p2_add` links.
Sourcing `scripts/setup/windows-gitbash-bootstrap-env.shs` does not change it.
The loadgen additionally needs TCP/thread system libraries, so a missing
library is the leading hypothesis — unconfirmed because the Err is not printed.
Fix: make every `Err` from `link_native_windows_with_engine`/`link_to_native`
reach stderr (`llvm_native_link_orchestrator.spl:708-719` prints only the
retention line), then fix the revealed cause. Related:
`windows_stage2_sanity_scv_prime_skipped_and_msvc_link_fallback_2026-10-25.md` §3.

**Diagnosed 2026-11-07.** The Err was not lost: it reached the worker error
text, but fused onto un-newlined `[bootstrap-error-count]` prints and outside
the truncated stderr tail. Revealed causes, in order:

1. `Linking failed: Windows GNU linking requires bootstrap-owned clang through CC`
   — `_link_native_mingw` (`_LinkerWrapper/shared_linking.spl`) demanded `CC`,
   while the runtime/entry objects had just been compiled with the verified
   PATH clang from `find_c_compiler`. Only the bootstrap scripts export `CC`.
   Fix: with `CC` unset, link with that same discovered clang
   (`mingw_link_driver_select`); a non-clang `CC` is still refused.
2. With `CC` set: `undefined symbol: rt_io_tcp_drain_line` — declared by
   `std.nogc_sync_mut.sffi.net`, defined only in the Rust runtime. Fix: C
   definition in `src/runtime/runtime_native.c` (+ `_WIN32` stub, header).
   With this, the admitted Stage 2 builds `loadgen.exe` (rc 0, CC set).

Also: the orchestrator now prints `[LLVM-LINK] error: link_to_native failed:
<detail>` on its own line at the failure site, and `link_to_native` resolves a
bare `windows` host to `windows-mingw`/`windows-msvc` from
`windows_link_flavor_for_config` (default MinGW). Pinned by
`test/01_unit/compiler/linker/windows_link_error_surface_spec.spl`.

**Still open:** on `_WIN32` every C-runtime `rt_io_tcp_*` is a stub returning
-1/nil (`runtime_native.c`, `#else /* _WIN32 stubs */`), so a C-runtime
Windows loadgen links but cannot open a socket. The compiler-side CC fallback
takes effect only once a Stage 2 containing it is admitted.

## 4. Full `simple_web_server` closure has many unrelated native gaps

The `main.spl` entry pulls 577 modules (async SSR, GPU, skia). Native MIR errors
there are off the AVX path: `gc_async_mut/gpu/engine2d/opencl_session.spl` (46),
`nogc_async_mut/http_server/config.spl` (39, incl. `for-in over non-array
iterables ... (#143)`, "assignment target has no local binding"),
`gpu/engine2d/cuda_session.spl` (20), `common/hpack/huffman_h2.spl` (8), skia (6).
For the perf test the vector lane should get its own small entry (sync
`SimpleHttpServer` + provider only) so these do not gate AVX measurement; the
gaps themselves stay open.

## Progress (2026-11-07, Stage 2 rebuilt from release `cea5d2682c5`, sha256 `58220b2c…`)

| item | fix | native proof |
|---|---|---|
| 1, 2 | #7359 trait-object move / `x!.field` dispatch | web server compiles past MIR |
| 3 | #7361 surface link Err, link with the runtime's clang, C `rt_io_tcp_drain_line` | loadgen links |
| 4 | #7355 `vector_main.spl` entry (577 → 6 modules) | builds |
| 5 | #7365 Winsock TCP/UDP in the C runtime (all `rt_io_*` were stubs) | server listens |
| 6 | #7379 `@cfg(baremetal or simpleos)` on dynlib's kernel SMF import; C `rt_dyncall_4/5/6` | web + loadgen link |
| 7 | #7384 float `Zero`/`Int` constants lowered with `fconst` (was `iconst.f64` → verifier `unreachable!`) | needs Stage 2 rebuild |
| 8 | #7397 `spl_print`/`spl_println` flush stdout (READY line stuck in buffer) | READY reaches log |

New items found on the way:

5. **Hosted native builds linked the SimpleOS kernel loader.** `os.posix.dynlib` →
   `dylib_async` → `os.kernel.loader` (ELF loader, PMM, paging, port I/O):
   undefined `pmm_*`, `rt_port_*`. Fixed in #7379.
6. **DB server: Cranelift verifier panic** `verifier/mod.rs:1634` (`iconst` of
   f64; trigger `f64?` unwrap nil path). The 0xC0000409 hint wrongly said
   "host commit limit exhausted". Fixed in #7384.
7. **Loadgen ↔ web server exchange fails on Windows**: warmup `ok=0 errors=8
   first_error=no-response:0 elapsed_ms=8`, then the 4-client pass segfaults;
   the server logs nothing after READY. OPEN (under investigation).
8. **`Some(<concrete>)` into a `Trait?` slot** still fails with the empty-type
   message (workaround in `pure_database.spl`). OPEN (fix in progress).
9. **Int literal to an `f64` parameter** (`takef(3)`) fails the verifier
   "arg 0 has type i64, expected f64". OPEN (fix in progress).
10. **Stage 2 phase verification matrix aborted on its RSS cap**
    (`status=rss-cap-exceeded`, peak 12813020 KiB vs cap 12784023 KiB,
    `cap_bound=small-host-one-worker`) while native perf builds ran
    concurrently; the cap is derived from free host memory at start. Rerun
    alone to tell a real regression from contention.

## Next

Rebuild Stage 2 with #7384 and the open fixes, rerun the native system perf
test alone, recalibrate the ratio bounds from the first native numbers.
