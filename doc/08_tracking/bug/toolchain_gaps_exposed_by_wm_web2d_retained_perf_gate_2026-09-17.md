# Toolchain gaps exposed by the retained WM Web2D perf gate - 2026-09-17

- **Status:** OPEN (filed 2026-09-17)
- **Severity:** P2 — three independent gaps surfaced by the new evidence gate
- **Lane:** macOS bug/todo db sweep 2026-09-17 — `check-wm-web2d-retained-perf-evidence.shs`
- **Host:** macOS 25.5.0, Apple M4 (aarch64)

The retained WM Web2D perf gate
(`scripts/check/check-wm-web2d-retained-perf-evidence.shs`, report
`doc/09_report/wm_web_2d_retained_perf_2026-09-17.md`) ran honestly on this
host and in doing so exposed three pre-existing toolchain gaps. Each is
independent; none blocks the gate's operation (it fails closed around them),
but each caps a lane the repo wants evidence for.

## Gap 1 — deployed binaries lack `spl_wffi_call_i64_into_bytes` (chrome lane)

The gate's Chrome lane (reusing `chrome_showcase/main.spl` verbatim) could
not produce any retained frame: the deployed self-hosted binaries do not
export `spl_wffi_call_i64_into_bytes`, so every Chrome-lane run errored
honestly. Distinct from the symbols in
`checked_i64_wffi_allocates_result_array_per_hot_call_2026-08-26.md`
(`spl_wffi_call_i64_checked`) and
`bootstrap_stage4_import_mangling_runtime_gap_2026-07-12.md`
(`spl_wffi_call_i64`) — this is the `_into_bytes` variant the web bridge
calls.

## Gap 2 — in-tree WM showcase entries do not compile

`examples/06_io/ui/widget_showcase_gui.spl` and
`graphics_2d_showcase_gui.spl` fail to compile with undefined
`showcase_resolution_wh` / `showcase_trace`. The gate therefore generates its
WM client into BUILD_DIR from the repo's shared modules instead. Once these
entry points compile, point the gate's driver template at them directly (the
generated client was a workaround, not a substitute).

## Gap 3 — `TextMetrics.char_count` JIT HIR fallback drops drivers to interpreter

A JIT HIR fallback on `TextMetrics.char_count` silently demoted the WM driver
module to the interpreter lane mid-session, so the gate's absolute frame times
(~11–12 s/frame at 320×240) are interpreted-lane figures, not native perf.
The evidence rows' existence/provenance stands; the perf numbers are not
native claims. Related-in-area but distinct from
`live_lane_inline_text_measure_counts_utf8_bytes_2026-08-11.md` (which is
about byte-vs-count semantics, not tier selection).

## Also re-confirmed (not new)

`rt_vulkan_copy_to_buffer_u32` is still absent from the deployed darwin
binaries — see `gpu_seed_feature_set_drift_2026-09-12.md`, re-measured
2026-09-17 by this gate (vulkan row: device probe ok, driver dies pre-bridge).

## Acceptance

- Chrome lane produces retained frames with a deployed binary (Gap 1).
- The two showcase entries compile and the gate uses them unmodified (Gap 2).
- `TextMetrics.char_count` compiles to native tier; gate numbers become
  native-lane claims (Gap 3).
