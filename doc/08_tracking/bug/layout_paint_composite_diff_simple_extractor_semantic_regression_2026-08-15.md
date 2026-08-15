# Chrome differential drivers: Simple-side extractor blocked by semantic regression

**Date:** 2026-08-15
**Status:** RESOLVED (2026-08-15)
**Found while:** re-running the Chrome rendering-comparison lanes.

## Symptom

All three differential drivers' SIMPLE extraction fails on the current tree,
so their retained evidence cannot be refreshed:

```
LAYOUT_DUMP_HTML=tools/layout_diff/fixtures/01_block_stacking.html \
  bin/simple run tools/layout_diff/simple_layout_dump.spl
error: semantic: invalid assignment: cannot assign field index on non-object value
```

Same failure shape for every fixture in `tools/layout_diff/`, `tools/paint_diff/`,
`tools/composite_diff/` ("FAIL simple extraction: <fixture>" for all 18; driver
verdict `ERROR — nothing was compared`). The CHROME side extracts fine
(Chrome for Testing 151.0.7922.34).

## Consequence for the gating specs

- `chrome_layout_differential_spec.spl`: 3/4 pass; only the fail-closed
  freshness gate fails (evidence of 2026-08-08 is older than checkout
  timestamps and cannot be regenerated while the extractor is broken).
- `chrome_paint_differential_spec.spl`: 3/4 pass, same freshness-gate failure
  (evidence of 2026-08-09).
- `chrome_composite_differential_spec.spl`: 0/3 — `tools/composite_diff/out/`
  has no retained summary at all on this checkout, and the extractor
  regression blocks producing one.

These failures are honest fail-closed verdicts, not lane defects.

## Evidence state after the refresh attempt

`tools/{layout_diff,paint_diff}/out/` is NOT git-tracked; the drivers begin with
`rm -rf out/chrome out/simple`, so the 2026-08-08/09 local evidence was replaced
by the broken run's output (chrome side present, simple side empty,
`fixtures_missing=18`). Until the extractor regression is fixed and the drivers
re-run, all three specs fail more examples than before — the pre-regression
verdicts recorded in this session were layout 3/4, paint 3/4, composite 0/3.

## Notes

- `bin/simple` is the Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`);
  the error is raised at semantic stage when loading the browser_engine renderer
  module graph, before any fixture work.
- The new vector-font lane (`tools/vector_font_diff/`,
  `chrome_vector_font_differential_spec.spl`) is unaffected (its Simple side
  uses the spl_fonts cdylib, not the browser_engine renderer) and passes 2/2.

## Resolution (2026-08-15)

**Root cause: Rust-seed interpreter regression, not a .spl defect.** The
interpreter grew a new interior-mutable class representation
(`Value::ClassInstance`, `src/compiler_rust/compiler/src/value.rs:1113`), but
the field-index assignment path (`obj.field[i] = v` / `self.field[i] = v`) in
`src/compiler_rust/compiler/src/interpreter/node_exec.rs` (case 2 of
`Expr::FieldAccess` targets) still matched only the legacy `Value::Object`,
so any class whose method writes `self.arr[i] = v` died with the reported
error. Minimal repro: a 10-line class with `me set(i,v): self.a[i] = v`.
The renderer path that tripped it is `_TreeStack` in
`src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`
(`self.nodes[idx] = ...`), reached from `parse_html`.

**Fix:** added a `Value::ClassInstance` arm to the field-index assignment
match in `node_exec.rs` (array/dict/tuple containers, mirroring the
`Value::Object` arm, updating via `ClassInstance::set_field`). Seed rebuilt
and redeployed to `bin/release/x86_64-unknown-linux-gnu/simple`.

**Evidence refreshed 2026-08-15:** all three drivers re-run;
`tools/layout_diff/out/summary.txt` (fixtures_compared=18, fixtures_missing=0),
`tools/paint_diff/out/summary.txt` (PASS — 18 fixtures, 16 divergences),
`tools/composite_diff/out/summary.txt` (PASS — 18 fixtures, 60 divergences).

**Spec verdicts (SIMPLE_TIMEOUT_SECONDS=600):**
- `chrome_layout_differential_spec.spl` executed=4 passed=4 failed=0
- `chrome_paint_differential_spec.spl` executed=4 passed=4 failed=0
- `chrome_composite_differential_spec.spl` executed=3 passed=3 failed=0
