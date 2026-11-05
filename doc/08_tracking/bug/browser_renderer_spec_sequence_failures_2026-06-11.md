# browser_renderer_spec — 22 residual failures (sequence-dependent + :has(> ) direct-child)

## Not closed 2026-09-13 — still open; re-verification blocked on this host

- **measured** `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
  (Rust seed v1.0.0-rc.1, Windows) ends `reason=outer-bound-timeout budget_ms=930000`,
  `executed=1 passed=0 failed=1 timeout=1` — the 98-test spec cannot complete here,
  so the 76/22 split can neither be confirmed nor refuted.
- **inferred** The `:has(> .badge)` cluster is a source-level defect in the renderer,
  untouched by anything since; nothing in the tree indicates it was fixed.
- Left OPEN: needs a Linux host where the spec finishes inside the runner budget.


Date: 2026-06-11
Status: open
Owner: gui-render-watch lane (gpu-backend-dx-harden session)

## Summary

After the gui-render-watch cycle 1-2 fixes (pushed as 6ff422d645:
selector_matcher, paint, script exec, currentColor, body bg extraction,
float/clear CSS APIs, dom set_style),
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
still reports **76 passed / 22 failed** in interpreter mode (measured
2026-06-11 ~16:12, pre stage4-deploy binary swap).

## Evidence gathered before the watcher agent was cut off

- Several failing tests PASS in isolation but FAIL when the full 98-test spec
  runs in sequence — renderer state accumulates across `it` blocks (suspect:
  module-level caches in the fallback pixel path or heuristic surface reuse).
- A second cluster is sequence-independent: `:has(> .badge)` direct-child
  selector tests (both the "applies" and "rejects nested descendant" cases,
  spec lines ~184-202). Traced so far: `normalize_child_combinators()`
  rewrites the `>` INSIDE `:has(...)` to ` > ` (it is depth-blind), after
  which the pseudo arg parses to `">  .badge"`; the `starts_with("> ")` +
  `substring(1).trim()` recovery in `pseudo_matches_node` looks correct, so
  the residual failure is further downstream (rule-application or the
  heuristic-vs-layout dispatch gate in
  `simple_web_engine2d_render_html_pixels`). Not yet root-caused.
- Failing-cluster spot list from isolation bisect (1-based it-block index):
  22, 24, 26, 28, 30, 32, 33, 34, 35 confirmed failing standalone; plus the
  sequence-dependent group around 10-20 that flips green standalone.

## Repro

```sh
bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl
# pre-deploy Rust-seed bin/simple: 76 passed / 22 failed
```

Note: repro currently blocked by the stage4 deploy seed gap — see
`doc/08_tracking/bug/stage4_deploy_no_seed_test_runner_blocked_2026-06-11.md`.

## Next steps

1. Fix `normalize_child_combinators` to be paren-depth-aware (do not rewrite
   `>` inside functional pseudo args) and re-measure the `:has(> )` cluster.
2. Find the cross-test state: render the same fixture twice in one process
   and diff pixels; suspect module-level memoization in the fallback path.
3. Re-bisect the sequence-dependent group after 1-2 land.

---

## 2026-11-05 re-verification on aarch64 Linux (work/libbug-std-rendspec-20261105)

Runner: Rust seed `build/phase_snapshots/phase1_1793422538/simple` (bin/simple
absent on this host — seed used as the documented substitute). Measured on
`origin/release/1.0.0` worktree: **130 executed / 112 passed / 18 failed**
(the June 98-test file has since grown; the 76/22 split no longer applies).

### Fixed in this lane (2 examples now green)

1. **`:has(> )` cluster**: already fixed on this tree —
   `normalize_child_combinators` is now paren-depth-aware and both
   `applies :has direct child selectors` and `rejects :has direct child
   selectors for nested descendants` PASS (they were not in the 18).
2. **`composites shorthand hex alpha background-color over the white page`**:
   real renderer bug. `parse_color` treated `#RGBA` as `#RGB` (dropped the
   alpha nibble, returned opaque black). Fixed to return byte alpha for
   `#RGBA`/`#RRGGBBAA`, and the software-lane canvas background now
   composites translucent canvas colors with the AUTHORED alpha fraction
   (`#0008` -> 8/15 -> 0x777777 over white) instead of the quantized byte
   (0x88 -> 120), which no byte-only integer blend can reconcile with the
   pinned `rgba(0,0,0,0.5)` -> 0x808080 oracle. Files:
   `simple_web_html_layout_renderer_foundation.spl` (parse_color),
   `simple_web_html_layout_renderer_paint_layout.spl` (authored-fraction
   canvas composite), `simple_web_html_layout_renderer.spl` (wire-in).
3. **`renders CSS flex row fixture pixels through BrowserRenderer`**: stale
   oracle, not a renderer defect. The fixture's two empty 80px flex items sit
   in an ~81px row; Blink parity (`test/01_unit/lib/blink/flex_spec.spl`
   "items with flex_shrink absorb overflow") and Chromium both shrink
   flex-shrink:1 items to fit (min-content 0), landing the right item at
   x 66..99. The pinned x=121 pixel predates shrink support. Oracle updated
   to x=80 inside the shrunken right item.

### Remaining 16 failures = seed-interpreter miscompilation, NOT renderer state

Bisect evidence (all runs deterministic, `--sequential`/`--threads=1`
invariant):

- All 16 pass when the same examples run in a smaller spec file (18-example
  bisect: 16/16 green; file-order prefixes to 65 examples: 0 failures;
  reversed full file: only the 2 standalone failures above).
- The renderer produces correct values in both process states: env-gated
  traces show identical correct style resolution, lane dispatch, and painter
  inputs for the same html; the failure signatures are index-arithmetic and
  helper-loop miscompilations in the SPEC's own expressions (e.g.
  `pixel_data[19 * TEST_WIDTH]` reads row 0's value; `_count_color` returns 0
  in the large compilation unit). Debug prints of indexed values disagree
  with `expect()` verdicts in the same example, i.e. the string-interpolation
  of `pixel_data[i]` itself miscompiles.
- The seed also emits `compiler_cross_module_private_symbol_collision`
  warnings for this exact compile, documenting JIT fallback-to-last-definition
  dispatch for ambiguous duplicates.

Conclusion: the 16 are context-dependent Rust-seed JIT compile defects in the
130-example compilation unit, not cross-test renderer state (the budget
latch, doc-pipeline cache, and engine slot pool were all audited and
exonerated: cache keys compare full html, the degrade latch is cleared on
begin and on cache hits). Per `.claude/rules/bootstrap.md` the remedy is the
pure-Simple self-hosted binary (absent on this host) or a seed compiler fix —
out of scope for this lane. Next step: re-run this spec under
`bin/release/<triple>/simple` when available; expect 130/130.
