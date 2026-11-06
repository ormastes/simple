# AVX server system perf: native build blockers with the admitted Windows Stage 2

Status: OPEN. Found 2026-11-07 on DESKTOP-5A4V03J (Xeon W-2135, AVX-512, MinGW
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

## 4. Full `simple_web_server` closure has many unrelated native gaps

The `main.spl` entry pulls 577 modules (async SSR, GPU, skia). Native MIR errors
there are off the AVX path: `gc_async_mut/gpu/engine2d/opencl_session.spl` (46),
`nogc_async_mut/http_server/config.spl` (39, incl. `for-in over non-array
iterables ... (#143)`, "assignment target has no local binding"),
`gpu/engine2d/cuda_session.spl` (20), `common/hpack/huffman_h2.spl` (8), skia (6).
For the perf test the vector lane should get its own small entry (sync
`SimpleHttpServer` + provider only) so these do not gate AVX measurement; the
gaps themselves stay open.

## Next

Fix 1+2 (native trait-object assignment/dispatch) and 3 (surface link errors)
in the pure-Simple compiler, rebuild Stage 2, add a vector-lane entry for the
web server, rerun the native system perf test.
