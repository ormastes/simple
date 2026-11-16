# slang model_loader specs error under `--mode=interpreter --clean` (private fn not visible)

**FIXED 2026-11-15**: the specs import fns the loader modules never exported; `loader.spl` and `transport.spl` now carry explicit `export` lines (module style of `core/page_manager.spl`). All four specs pass (7/7, 4/4, 3/3, 5/5) under `--mode=interpreter --clean`; readiness gate `STATUS: PASS`.

Found 2026-11-15 on Windows seed (`/c/dev/simple/bin/simple.exe`, 37622272 bytes).

`check-llm-runtime-slang-local-readiness.shs` runs each sub-spec with
`test <spec> --mode=interpreter --clean`. Four of them end `outcome=ERROR executed=0`:
`model_loader_manifest_spec`, `..._tensor_bytes_spec`, `..._stream_plan_spec`, `..._transport_spec`:

    error: semantic: private fn `load_model_from_manifest_text` of module
    `std.gc_async_mut.slang.model_executor.model_loader.loader` ... is not visible to
    test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl; mark it `pub` or `export` it

The same specs PASS (11/11, 4/4, 3/3, 5/5) without `--mode=interpreter --clean`, so the
readiness gate (and the native-streaming-evidence / setup-contract gates that nest it)
cannot go green on this host regardless of timing. (Decision taken: spec imports are valid, export the fns;
the seed visibility check is left as is.) Original question:
visibility used by the default mode (seed fix).

## Timeout measurement (same session)

The three nested gates used to time out at 900 s. Host spawn cost measured 2026-11-15:
`sh -c true` 24 s, empty `$(true)` subshell 7 s, `$(wc|tr)` 21 s, `$(sha256sum|awk)` 26 s.
The readiness manifest loop did ~8 subshell pipelines per file; replaced with one `wc` and
one `sha256sum` over all files. Readiness gate wall time: >900 s (timeout) -> 188 s to a verdict.

## Seed cannot parse the current tip's smux V4 (blocks live caret spec in this worktree)

`caret_slang_local_hello_system_spec` (live) fails in this worktree before reaching slang:
`compile failed: parse: src/os/apps/smux/runtime_primary_control_service_v4.spl: Unexpected
token: expected expression, found Assign at line 131, column 41` (one-line `else: x[i] = v`
statement form, commit ae72214b9c2). The Rust seed at /c/dev/simple/bin/simple.exe
(37622272 bytes) predates it. The default-model-id fix in that spec is therefore
unverified live here; the 2026-11-14 matrix tree (older) did not contain that file.
