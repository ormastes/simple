# Session Regression Sweep — 2026-08-08

## Top line
**10 suites clean (PASS), 0 new regressions, 0 infra-timeouts (1 borderline internal 120s runner-timeout treated as pre-existing/flaky), 4 pre-existing-known failures of 14 total suites.** (`mir_lowering_new_spec.spl`'s pre-existing classification is now substantiated by an A/B test against the pre-`a399483d` file content — see `doc/08_tracking/bug/mir_lowering_new_spec_preexisting_failures_2026-08-08.md` — not just "spec untouched" reasoning.)

## Critical finding: "deployed bin/simple" is the Rust seed, not the self-hosted binary

`bin/simple` (symlink -> `bin/release/x86_64-unknown-linux-gnu/simple`, rebuilt
2026-08-08 00:53) prints on every run:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

No larger/differently-shaped pure-Simple self-hosted binary exists anywhere
newer than the seed (checked `bootstrap/stage{1,2,3}/simple`,
`src/compiler_rust/target/{release,bootstrap}/simple`, `bin/release/**`). The
"bin/simple was redeployed twice today, latest carries the coverage `<entry>`
fix + blend-span kernels + JIT named-fn guard" claim in the task brief could
not be verified against a self-hosted artifact — the artifact currently live
at `bin/simple` is the Rust seed. This entire sweep therefore measured the
**seed's** behavior, per the project rule "Default tooling = pure-Simple
self-hosted binary... Seed is bootstrap-only" — the deployed tool violates
that rule right now. Flagging loud per instructions; not fixed (verification
pass only).

## Suite results

| Suite | Verdict | Classification |
|---|---|---|
| test/01_unit/compiler/mir/mir_lowering_new_spec.spl | FAIL 15/34 (19 failed) | PRE-EXISTING — spec untouched by today's commits except an unrelated docs-only commit (`cfe0506e336`); failures are LLVM/backend alignment checks (`arg_ty = self.valid_llvm_type(...)`, `defining_module not found`) unrelated to the touched areas |
| test/01_unit/compiler/mir/mir_lowering_repair_contract_spec.spl | PASS 2/2 | clean |
| test/01_unit/compiler/interpreter/tiered_jit_hotspot_spec.spl | FAIL 47/51 (4 failed) | PRE-EXISTING — matches long-standing `doc/08_tracking/bug/jit_hotspot_verification_process_storm_2026-05-29.md`; spec last touched by unrelated WP-H/WP-J commits, not today's touched areas |
| test/perf/graphics_2d/cpu_simd_spec.spl | PASS 20/20 | clean |
| test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl | PASS 3/3 | clean |
| test/integration/rendering/engine2d_backend_spec.spl | PASS 8/8 | clean (use-warnings for `simd_kernels` symbols are non-fatal import-graph noise, not failures) |
| test/01_unit/browser_engine/browser_renderer_spec.spl | FAIL — internal 120s runner timeout, Results: 1 total, 0 passed, 1 failed | PRE-EXISTING — matches long-standing `doc/08_tracking/bug/browser_renderer_spec_sequence_failures_2026-06-11.md`; spec last touched by unrelated WP-H commit |
| test/01_unit/browser_engine/html_tree_builder_spec.spl | PASS 33/33 | clean |
| test/01_unit/os/compositor/compositor_spec.spl | PASS 32/32 | clean |
| test/01_unit/os/compositor/host_compositor_core_coverage_closure_spec.spl | PASS 12/12 | clean (relevant to today's coverage `<entry>` attribution fix) |
| test/02_integration/rendering/wm_pixel_pipeline_spec.spl | PASS 18/18 | clean |
| test/01_unit/os/compositor/wm_core_spec.spl | PASS 16/16 | clean |
| test/03_system/gui/web_css/web_css_text_layout_spec.spl | FAIL 5/6 (1 failed) | PRE-EXISTING — matches the known line-height flake called out in the task brief |
| test/01_unit/app/spl_coverage_spec.spl | PASS 3/3 | clean (relevant to today's coverage `<entry>` fix) |

All runs produced an explicit `Results: N total, ...` verdict line; none were
killed (no exit 124/143/255 observed). No suite exhibited a new failure
attributable to today's touched areas (MIR lowering, JIT, engine2d SIMD,
browser-engine renderer, compositor, WM, web_css, coverage tooling).

## Method notes
- Each spec run via `bin/simple run src/app/test_runner_new/test_runner_single.spl <spec> --no-session-daemon --sequential`, foreground, one spec per invocation.
- 14 spec files enumerated from `git grep`/`find` across the 8 named touch areas (`test/`), preferring the canonical non-`.spipe_matchers_*` spec files.
- `browser_renderer_spec.spl`'s failure is an internal test-runner 120s timeout (not a Bash-tool kill), still produced a `Results:` line, and is classified pre-existing on the strength of an existing dated bug doc plus no relevant commit touching the spec or its target module today.
