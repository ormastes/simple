# AOP hart hooks: no in-tree path executes woven advice for lib-module hardware code

**Date:** 2026-07-22
**Severity:** High (blocks Phase-3 "AOP hart hooks" from being AOP-carried end-to-end)
**Found by:** Lane H (AOP hart debug hooks, `src/lib/hardware/debug_hooks/`)
**Evidence:** `bin/simple run test/01_unit/lib/hardware/debug_hooks/hart_debug_probe.spl`

## Resolution status (updated 2026-07-22, Lane SS)

- **Gap 2 — FIXED (.spl).** `compiler.frontend.core.aop.matches_predicate` now
  routes parser-tokenized pointcut predicates (any predicate containing `(`) to
  a new `aop_pointcut_matches`, a byte-mirror of the interpreter-side
  `interp_aop_predicate_matches` (execution/call selectors + `& | ! ()`
  combinators + the same intentionally-limited glob). Regression witnesses:
  - `hart_debug_probe.spl` Gate 6 now asserts the tokenized
    `execution ( * hart64_step_body ( .. ) )` predicate weaves >0 (was pinned at
    0/fail-closed), AND a NEW case pins a genuinely-unmatchable
    `execution ( * no_such_hart_fn ( .. ) )` predicate at requested=1/woven=0 so
    the W2-B fail-closed signal stays regression-tested.
  - NEW `test/01_unit/compiler/frontend/core/aop_pointcut_matcher_parity_probe.spl`
    asserts the MIR-path and interp-path matchers agree over 20 predicates incl.
    prefix/suffix/middle-glob edge cases — the "cannot diverge again" guard.
  Full AOP/weaving spec suite (predicate_parser, weaving_config, ordering,
  conflict_detect, mir/aop_injection, mdsoc/weaving_support, mdsoc/aop_proceed,
  interpreter_aop_weave, core/aop_complete) all pass unchanged; matcher change is
  false→true only for tokenized predicates, so blast radius is bounded.

- **Gap 1 — still OPEN, seed-side (characterized, not fixed).** The run-path
  weaver is the Rust bootstrap seed's interpreter (`bin/simple` prints the
  "bootstrap seed only" banner), whose entry-module-only weaving is baked into
  Rust, not `.spl`. `hart_dbg_step_hook_fires()` therefore remains 0 on
  `bin/simple run` at this tip (printed loudly, not hidden). No `.spl`-only fix
  can flip that witness on the deployed binary; it requires the self-hosted
  compiler deploy (bootstrap blocker tracked in memory/bootstrap docs). Per the
  no-patch-Rust constraint this gap is left characterized. Bug-doc fix #3 (flip
  the `step_hook_fires=0` print into a hard assertion) stays deferred until the
  self-hosted deploy lands.

## Summary

`src/lib/hardware/debug_hooks/hart_debug.spl` declares the Phase-3 hart debug
aspect (`on pc{ execution(* hart64_step_body(..)) } use hart_dbg_on_step before
priority 10`, plus the rv32 twin) on the rv64/rv32 core step join points.
Two independent defects mean NO in-tree pipeline path can execute that woven
advice today; the hooks therefore ship as an executable seam
(halt/step/pc-trace all gated green) plus an aspect declaration wired for the
full pipeline, with `hart_dbg_step_hook_fires()` as the weave-executed witness
(currently 0 on the run path — printed loudly by the probe, not hidden).

## Gap 1 — interpreter weaving is entry-module-only

The run-path weaver (seed interpreter; also `interpreter_aop_weave.spl`
call_hir_function hook by design) only advises functions DEFINED in the entry
module:

- aspect + target + call all in the main file → advice fires (verified: 3/3).
- aspect in main file, target `hart64_step_body` defined in the imported
  `std.hardware.debug_hooks.hart_debug` module, called directly from main →
  0 fires (verified).
- aspect declared at module level inside the imported module → 0 fires
  (verified; module-level `on pc{...}` declarations of imported modules are
  not collected on the run path).

Consequence: aspects targeting stdlib/hardware modules (the whole point of
hart hooks, log instrumentation, JTAG DM attach) can never execute on the
interpreter path. Only main-file-local toy targets weave.

## Gap 2 — MIR weave matcher rejects parser-shaped execution(...) predicates

`compiler.frontend.core.aop.matches_predicate` (used by `weave_function`, i.e.
the full driver_pipeline.weave_aop path) matches bare names, globs, `@attr`,
`module:`, `effect:`, and `join:` forms — but NOT the space-tokenized
`execution ( * name ( .. ) )` predicate_text that `parse_pointcut_text`
produces for standard `on pc{ execution(* name(..)) }` declarations
(`interpreter_aop_weave_spec.spl` documents that tokenized shape; the
interpreter-side matcher handles it, the MIR-side matcher does not).

Verified through the driver's own machinery (probe Gate 6):
- rule predicate `"hart64_step_body"` (bare) → advices_inserted=2,
  `aop_weave_count()`=2.
- rule predicate `"execution ( * hart64_step_body ( .. ) )"` (what the parser
  emits) → advices_inserted=0, `aop_weave_count()`=0 with requested=1.

Thanks to W2-B (0c5210c8ff2) this is at least FAIL-CLOSED in VHDL generation
(requested>0, woven=0 → CodegenError instead of hollow RTL), but it means
every spec-grammar execution-pointcut aspect is un-weavable on the full
pipeline until the matcher understands the tokenized form (or HIR lowering
normalizes predicate_text to the glob form before storing it).

## Additional blocker (deployment, already tracked elsewhere)

Even with Gap 2 fixed, executing the FULL self-hosted pipeline
(driver_pipeline.weave_aop → mir_aop_injection → run woven code) in-tree
requires the deployed pure-Simple compiler binary; the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` is the Rust bootstrap seed,
whose interpreter has Gap 1. (Self-hosted deploy blocker tracked in the
bootstrap docs/memory.)

## Fix directions

1. Interp weaver: collect `HirAopAdvice` from ALL loaded modules and apply the
   call_hir_function hook to imported-module calls (matching by qualified or
   bare name, mirroring MIR-path semantics).
2. Either teach `matches_predicate` the tokenized `execution ( ... )` form
   (delegating to the same matcher `interpreter_aop_weave` uses), or normalize
   predicate_text at HIR-lowering time so both weavers consume one canonical
   form. Add a cross-matcher parity spec so the two paths cannot diverge again.
3. Regression gates: flip the hart-debug probe's
   `INTERP WEAVE GAP: step_hook_fires=0` print into a hard
   `step_hook_fires > 0` assertion once (1) lands; the probe already asserts
   the W2-B fail-closed signal for (2).

## Repro

```
cd <repo>
bin/simple run test/01_unit/lib/hardware/debug_hooks/hart_debug_probe.spl
```

All 16 gates pass today: seam behavior (trace/halt-freeze/single-step/resume,
rv64+rv32) green, weave accounting >0 via bare-name rule, tokenized
execution-form rule pinned at 0/fail-closed, interp gap printed explicitly.
