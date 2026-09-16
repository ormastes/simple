# Seed interpreter: stack overflow in 'trim' (recursion depth 1000) loading browser_engine module graph

- **ID:** seed_run_trim_recursion_overflow_browser_engine_2026-07-19
- **Status:** OPEN
- **Severity:** medium (blocks `bin/simple run` on any program importing the
  browser_engine module graph; compounds the tracked test-runner init hang)
- **Lane:** Rust bootstrap seed, hosted Linux (`bin/simple run`)

## Symptom
Running a small hosted probe that imports
`src/lib/gc_async_mut/gpu/browser_engine/` (to read
`fb_generated_widget_chrome_text` values) aborts during module-graph load:

```
stack overflow: recursion depth 1000 exceeded limit 1000 in function 'trim'
```

The failure is in the seed's interpreter while loading/preprocessing the
module graph — before user code runs.

## Context / impact
Found 2026-07-19 while mapping Aqua golden-regen recipes. With
`bin/simple test` already unusable on these paths
(deployed_seed_test_runner_init_hang_2026-07-17.md — daemon init hang,
reconfirmed today on all 6 theme-affected UI/compositor specs), this closes
the second hosted verification route. Net effect: **deploying a working
self-hosted `bin/simple` is a hard prerequisite** for hosted golden
regeneration and for running the theme-affected spec set.

## Repro
Scratchpad probe script importing the browser_engine module graph via
`bin/simple run` (see session scratchpad golden-regen-recipe.md, 2026-07-19).
Any minimal .spl importing `gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer`
should reproduce.

## Fix direction
Seed-side: make 'trim' (or its caller loop in module preprocessing)
iterative or raise/eliminate the recursion — likely a pathological input in
one of the large browser_engine sources (e.g. multi-thousand-entry literal
arrays around simple_web_html_layout_renderer.spl:6959-7013). Preferred per
repo policy: land the self-hosted redeploy and retire seed-lane usage here.
