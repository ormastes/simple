# Interpreter lane: three raw SFFI boundaries abort (or fabricate) instead of returning their documented failure sentinel

Date: 2026-09-05
Status: SUPERSEDED
Area: compiler/interpreter externs, SFFI
Found by: `test/03_system/plan_acceptance/sffi_universal_admission_next_spec.spl`

## Summary

Three raw boundaries have a documented fail-closed contract on the Simple side,
but the seed interpreter lane does not honour it. Two abort the whole
interpreter; one fabricates a plausible-looking handle. In every case the
documented failure value is unobservable to a caller in that lane, so the
Simple-side `Result`/sentinel contract is dead code there.

| boundary | documented failure | interpreter lane actually does |
|---|---|---|
| `spl_dlopen` (registered at `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2635` -> `wsffi::spl_dlopen`) | non-positive handle -> `Err("E-SFFI-001: failed to load provider: …")` (`src/lib/nogc_sync_mut/sffi/dynamic.spl:56`) | raises `spl_dlopen failed for '<path>'` and aborts |
| `rt_file_mmap_read_bytes` | nil -> `Err("file mmap read failed: …")` (`src/lib/nogc_sync_mut/io/file_ops.spl:199`) | raises `rt_file_mmap_read_bytes failed: No such file or directory (os error 2)` and aborts |
| `rt_webgpu_create_surface` (`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:2937`) | `WEBGPU_INVALID_HANDLE = -1` (`src/runtime/hosted/webgpu.rs:52`) | returns `Value::Int(0)` — a plausible handle, not the sentinel |

## Why it matters

`0` from `rt_webgpu_create_surface_fn` is indistinguishable from a real surface
handle at the call site, which is the exact "never manufacture a success-shaped
value" failure the SFFI universal-admission plan exists to remove
(`doc/03_plan/compiler/sffi/sffi_universal_admission_next_2026-08-25.md`). The
two aborting boundaries are worse than a wrong value: no caller can fail closed
at all.

## Current mitigation (pure Simple, landed 2026-09-05)

Callers now reject inputs that can never succeed before entering the raw
boundary, and normalise the WebGPU result:

- `src/lib/nogc_sync_mut/sffi/dynamic.spl` `_sffi_dlopen_checked` — empty path,
  or a path (containing `/`) whose artifact is absent, returns `Err`. Bare
  sonames still reach the loader's own search path.
- `src/lib/nogc_sync_mut/io/file_ops.spl` `file_mmap_read_bytes` / `file_mmap`
  — empty or non-existent path (and non-positive extent / negative offset for
  `file_mmap`) fail closed with `Err` / `-1`.
- `src/lib/nogc_sync_mut/gpu/engine2d/webgpu_sffi.spl`
  `webgpu_sffi_create_surface` — normalises any non-positive provider result to
  `WEBGPU_INVALID_HANDLE`, and short-circuits when the provider is unavailable.

These are workarounds at the caller, not fixes at the boundary. A path that
exists but is unreadable, or a genuinely failing provider, still aborts.

## Unblock condition

The seed's interpreter extern dispatch must return the documented sentinel /
nil for these three symbols instead of raising, and
`rt_webgpu_create_surface_fn` must return `-1`, not `0`. Once that lands, the
caller-side existence probes above can be removed.

## 2026-11-10 p2fix-interp lane (work/p2fix-interp-20261110, base d8c0a761988c) — VERIFIED

All three boundary fixes are present at this base and were executed against a
fresh cargo build of the seed from this tree (the 2026-11-07 deployed seed
bin/simple.exe predates them: its spl_dlopen still raised and
rt_webgpu_create_surface still returned 0; rt_file_mmap_read_bytes already
returned nil). Fresh-build probe on BOTH interpret and jit lanes:
spl_dlopen(missing) -> 0, rt_file_mmap_read_bytes(missing) -> nil,
rt_webgpu_create_surface(640,480) -> -1. Retained Rust unit tests all pass:
wsffi::dlopen_load_failure_returns_zero_not_abort,
file_io::mmap_named_text_and_bytes_match_read_contract,
gpu::webgpu_create_surface_returns_invalid_handle_not_zero.
New regression spec
test/01_unit/compiler/95.interp/interpreter/raw_boundary_failure_sentinels_spec.spl
(4/4 seed-smoke). Caller-side existence probes in nogc_sync_mut remain as
defense in depth; removal is a separate cleanup.

## Addendum 2026-11-11 — lane interp5 verdict: SUPERSEDED-by-prior-lane (spot-check confirms)

Verdict: **SUPERSEDED** — the 2026-11-10 p2fix-interp lane addendum above is
accepted; this lane re-verified on the 2026-11-11 refreshed tracked seed
(`bin/simple.exe`, 2026-11-11 build) rather than redoing deep triage. Prior-lane
base `d8c0a761988c` is an ancestor of this lane's base `b364745fdbf8`, so the
verified fixes are in this tree; the seed refresh commit (`a104e85c3541`,
tracked-seed refresh from the release tip) carries them into the deployed
binary. The durable fix artifacts are the retained Rust unit tests
`wsffi::dlopen_load_failure_returns_zero_not_abort` and
`gpu::webgpu_create_surface_returns_invalid_handle_not_zero` plus the
regression spec below.

Seed-smoke spot-check (2026-11-11, lane interp5, refreshed seed
`bin/simple.exe` 2026-11-11 build, `SIMPLE_LIB=src`, `--mode=interpreter
--no-cache`): `test/01_unit/compiler/95.interp/interpreter/raw_boundary_failure_sentinels_spec.spl`
→ 4 total / 4 passed. No further action; caller-side existence-probe removal
remains the separate cleanup recorded by the prior lane.
