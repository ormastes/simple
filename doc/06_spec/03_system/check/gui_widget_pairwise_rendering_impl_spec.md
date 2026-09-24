# GUI widget pairwise evidence status

**Source:** `test/03_system/check/gui_widget_pairwise_rendering_impl_spec.spl`

**Audience:** GUI renderer and test maintainers
**Status:** Incomplete pairwise rendering evidence; focused test execution UNKNOWN on 2026-09-26

## Purpose

Count the dimension pairs represented by the spec's 30 sample rows, reject
duplicate-row inflation, and witness one GUI button emitting a command through
the shared DrawIR producer. This manual describes the executable scenarios;
it does not certify final pixel rendering or backend parity.

## Preconditions

Use an admitted, working pure Simple runtime. The test's system-test cover
annotation is intentionally absent because it audits evidence status rather
than claiming source branch coverage. Supply `--no-cover-check` for this run.

```sh
bin/release/aarch64-apple-darwin-macho/simple test \
  test/03_system/check/gui_widget_pairwise_rendering_impl_spec.spl \
  --mode=interpreter --no-cover-check
```

## Scenarios

1. **Sample coverage is incomplete.** The test builds 30 rows, counts six
   pair categories from the row values, expects 134 distinct pairs, and
   expects `incomplete` against the historic 831-pair target.
2. **Duplicates do not inflate coverage.** Repeating the first row still
   yields six distinct pairs and `incomplete`.
3. **GUI uses shared DrawIR.** A real button node is projected with
   `widget_tree_to_draw_ir_cpu`; the emitted composition contains its
   component ID.

## Limits and recovery

The row values are inventory data only. They are not applied to widget layout,
theme or viewport, and no pixel buffer is captured. The DrawIR witness covers
one button, not all widget kinds. The local pure Simple binary exited 139
during discovery on 2026-09-26; no scenario verdict was obtained from it.
When the runtime is repaired, rerun the command above before treating these
assertions as executed evidence. Full coverage requires current widget inventory,
real row-specific scenes, backend execution and final pixel oracles.
