# browser_renderer_spec — 22 residual failures (sequence-dependent + :has(> ) direct-child)

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
