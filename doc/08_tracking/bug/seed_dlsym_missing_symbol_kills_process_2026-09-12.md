# Seed: `spl_dlsym` on a missing symbol raises and kills the process; `*_checked` dispatch loses the `*mut i64` writeback

- Status: OPEN (2026-09-12) — found by the EGL package-2 lane (agent U) while building the callable map; not fixed here
- Found: 2026-09-12
- Component: seed SFFI/dynlib surface — `spl_dlsym`, `sym_checked`, `resolve_i64_checked`, `VersionedDynLib.has_symbol`, the `*_checked` dispatch family; `rt_host_dynlib_symbol`
- Lane: interpreter (deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-06 09:59)

## Observation

1. `spl_dlsym` on a symbol that the library does not export **raises and terminates the process** instead of returning a refusable value. `sym_checked`, `resolve_i64_checked` and `VersionedDynLib.has_symbol` inherit the same behaviour, so there is no in-language way to probe a symbol's presence. `rt_host_dynlib_symbol` returns 0 for the same case — inconsistent across the two surfaces.
2. The whole `*_checked` dispatch family returns `Ok(0)` for a call that really produced 222: the `*mut i64` out-parameter writeback is lost (the 2026-09-11 record for this writeback bug applies; the callable map rides the direct-return `spl_wffi_call_i64` instead).

## Consequence

Any admission path that needs "is this symbol present?" must either avoid the seed surface or accept a process-killing probe. EGL package 2's `callable_map_v1` added `src/lib/nogc_sync_mut/sffi/dynlib_exact_admission_v1.spl` as its own boundary for exactly this reason.

## Fix direction

Make missing-symbol resolution a value (`nil`/typed refusal) at the `spl_dlsym` boundary in the seed and in the Rust twin; align `rt_host_dynlib_symbol`; pin with a spec that resolves one present and one absent symbol from a `cc -shared` fixture and asserts the process survives. Restore the `*mut i64` writeback in the `*_checked` family with a value-returning spec (222 must come back as 222).

## Related

- EGL receipts 2026-09-12, package 2 (`environment_optimized_dynamic_libraries_receipts_2026-09-12.md`, branch `work/egl-wave-2026-09-12`)
