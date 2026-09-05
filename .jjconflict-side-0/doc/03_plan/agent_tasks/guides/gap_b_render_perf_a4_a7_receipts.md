# Guide B3 — render_perf A4/A7: the two receipt modules the acceptance spec imports

Owner: one sonnet-class agent (ui/render). Follow literally. A5/A6/A8 need
physical hardware and are NOT in this guide.

## Signatures to land (exact — the spec imports these names)

1. `src/app/wm_compare/production_native_cpu_draw_ir_frame.spl`

```simple
fn production_native_cpu_draw_ir_frame_receipt(width: i64, height: i64, frames: i64) -> text
```

Returns a receipt as `key=value` lines (one per line, same shape as
`strict_semantic_vulkan_producer_receipt` in
`src/app/wm_compare/strict_semantic_vulkan_producer.spl` — copy its field
naming). Required keys the spec reads:
`producer_receipt_selected_backend` (must be `cpu-drawir` when the CPU DrawIR
path really executed), `producer_receipt_fallback_used` (`false` only when no
fallback happened; `true` otherwise — never omit it). Add the other A4 fields
from the plan text (considered/culled command counts, p50/p95, max RSS,
checksum, readback source/count, completion) with real measured values; the
spec does not read them yet but the plan requires them.

2. `src/app/wm_compare/render_perf_aggregate.spl`

```simple
fn render_perf_aggregate_receipt(width: i64, height: i64, frames: i64) -> text
```

Keys the spec reads: `aggregate_receipt_a4_p95_within_budget`,
`aggregate_receipt_a5_p95_within_budget` (`true`/`false` against
12,500,000 ns), `aggregate_receipt_fallback_used`,
`aggregate_receipt_a6_correlated` (`true` only when a real A6 receipt file
under `build/render_perf/physical_8k80/` correlates), and
`aggregate_receipt_status` — `pass` only when everything above is true,
`blocked-physical` when A4+A5 pass but A6 is absent, `failed` otherwise.

Write a unit spec for the correlator's interim `blocked-physical` verdict at
`test/01_unit/app/wm_compare/render_perf_aggregate_spec.spl` — that contract
belongs there, not in the plan-acceptance spec.

## Acceptance

```
SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/render_perf_redesign_plan_spec.spl
```

- A4 `it` passes (`selected_backend=cpu-drawir`, `fallback_used=false`).
- A7 `it` — on a host WITHOUT the physical A6 receipt it stays RED at
  `aggregate_receipt_status: expected blocked-physical to equal pass`; that is
  the honest state. Your unit spec proves the interim verdict; A7's box stays
  open until A6 evidence exists.
- No `E1034` in the run.

Tick A4 in `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md:43`
ONLY with `— verified <command> → A4 ✓, <date>`. Do not tick A7.
