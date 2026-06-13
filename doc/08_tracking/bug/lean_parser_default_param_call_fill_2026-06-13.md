# Lean frontend: default-param call-site application NOT implemented (DEPLOY-BLOCKER)

- **ID:** lean_parser_default_param_call_fill
- **Severity:** P1 — **DEPLOY-BLOCKER** for removing the self-hosted-frontend
  delegation. NOT a soft deferral: if the lean frontend is deployed (delegation
  removed) before this is built, omitted-argument calls to functions with default
  parameters **silently miscompile** (the omitted slot passes 0 / uninitialized,
  not the default expression). Common feature → silent wrong results.
- **Date:** 2026-06-13
- **Component:** `src/compiler/20.hir` / `src/compiler/30.types` — call lowering /
  call-signature resolution (self-hosted pipeline).
- **Status:** OPEN. Parser + IR-capture half DONE (commit fce662c707d1); call-site
  *application* half not started (own milestone).

## What works (commit fce662c707d1)
- The lean parser accepts `fn f(x: T = expr)` in both param-parsing sites
  (`parse_fn_decl`, `parse_class_body_method`). This cleared real-world parse
  blockers (e.g. `src/lib/nogc_sync_mut/mcdc.spl:187` `minimum: f64 = 100.0`).
- Per-param default expr ids are faithfully captured in the IR: stored via
  `decl_set_param_defaults` on the decl text-field store, read back by the flat
  bridge (`convert_decl_fn`) which populates `Param.has_default` / `Param.default`;
  `lower_param` carries them into `HirParam`. Defaults are NOT discarded.
- **Explicit-arg calls are correct** end-to-end on stage4: `greet("hi", 5)` → 10.

## What does NOT work (the gap)
- **Omitted-arg calls do not apply the default.** Stage4 e2e:
  `greet("hi")` (default `count = 3`, body sums `name.len()` `count` times) returns
  **0**, not 6 — the omitted parameter is zero-filled, the default expr is never
  substituted.

## Root cause
The self-hosted pipeline has **no infrastructure** to apply defaults:
- HIR call lowering (`20.hir/hir_lowering/expressions.spl:108–117`) lowers callee +
  args verbatim — no param lookup, no missing-arg detection.
- There is **no value-arg arity check anywhere** (`30.types`, `20.hir`, `40.mono`
  only validate *type*-arg counts in monomorphization; macros have their own).
- There is no call-signature resolution point where the callee's `HirParam.default`
  list is reachable at the call site.
So a missing trailing arg is neither filled nor flagged — it silently becomes 0.
This predates the parser change; the parser change merely makes such call sites
*reachable* (previously the file failed to parse).

## Fix sketch (its own milestone — needs call-resolution that doesn't exist yet)
1. At the point a call's callee resolves to a function symbol (type-check or a new
   resolution pass), fetch the callee `HirFunction`'s params.
2. If `call.args.len() < params.len()` and every missing trailing param
   `has_default`, append each param's `default` expr (clone) to the lowered args.
3. If a missing param has no default → emit a real "too few arguments" error
   (this also fills the currently-absent value-arg arity check).
4. Verify with `tmp/site12/g51_defparam.spl`: `omitted=` must become 6.

## Deploy gate
Add to the M12 deploy-gate checklist (next to delegation-removal): **call-site
default-fill implemented + `g51_defparam` omit-call correct** must be GREEN before
the self-hosted frontend deploys without delegation.
