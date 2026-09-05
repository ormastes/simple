# Phased Burndown: Re-enabling the Dormant Type Checker

Status: **warn-only wiring landed; fatal enablement blocked on burndown + wall.**
Source finding: `doc/08_tracking/bug/deep_recheck_2026-07-05.md` (Type system, P1/P2).

## 1. Confirmed findings (current source, with citations)

The entire Phase-3 semantic layer is dormant. Verified by direct source read:

1. **Phase-3 type checking is a NO-OP.**
   - `src/compiler/80.driver/driver.spl` `type_check_impl()` (~613) is an explicit,
     documented no-op: *"kept for API compatibility but is a no-op."*
   - The real Phase-3, `lower_and_check_impl()` (~423-567), does HIR lowering only in
     the native (`sources > 0`) path — it never constructs the inference engine.
   - The HM inference engine `HmInferContext` (2552 LOC across
     `src/compiler/30.types/type_infer/`) — with real `unify`, occurs-check, and
     `TypeInferError.Mismatch` emission — has **zero callers** outside `30.types`.
     Its module entry `infer_module` (`type_infer/inference_control.spl:594`) is
     never invoked. `HmInferContext` appears in the driver only inside a stale
     comment (`driver.spl:555`).

2. **Generic trait-bound (`where T: Trait`) never checked.**
   - `resolve_methods_with_solver` (`src/compiler/35.semantics/resolve.spl:712`) —
     the variant documented to do *"trait bound checking during method resolution"* —
     has a stub body: `# Bootstrap fallback ...` `return (module, [])`.
   - The wired `resolve_methods` (`resolve.spl:695`) does UFCS method resolution only,
     no bound checking. (It is itself only called in the driver's `sources <= 0`
     bootstrap branch, not the native path.)

3. **Visibility/privacy enforcement never wired.**
   - `check_module_visibility` (`src/compiler/35.semantics/visibility_integration.spl:11`)
     is a complete HIR walker returning `[VisibilityWarning]`, exported by
     `35.semantics/__init__.spl:101` — but had **zero callers**. Visibility has zero
     effect at compile time.

4. **(Related) Effect inference is also stubbed.** `run_effect_pass`
   (`src/compiler/30.types/type_system/effect_pass.spl:24`) — the one type-system pass
   referenced by the driver (bootstrap branch only) — early-returns
   `(modules, empty_warnings)` at line 26-27; the real body below is dead.

Root cause pattern: these passes were **deliberately stubbed / left unwired** to keep
the stage4 bootstrap building. Enabling any of them fatal, unverified, would very
likely reject code that compiles today and break the ~993-module build.

## 2. Decision: warn-only, opt-in wiring (landed)

Rationale:
- The engine has **never** run over the full module set, so its true diagnostic
  count is unknown. Empirically measuring it requires a fresh compiler build, which
  is **wall-gated** (seed miscompiles; pure-Simple bootstrap is slow). We could not
  count diagnostics in-session.
- An unconditional run — even warn-only — risks a **crash** in the never-exercised
  2552-LOC engine on the fragile stage4 binary, which would break *every* build.
  Simple has no exception catch (Result-only), so an engine panic/SIGSEGV cannot be
  contained at the call site.
- Therefore the wiring is **gated behind `SIMPLE_TYPECHECK_WARN=1` (default OFF)** and
  only **logs** diagnostics — it never pushes `ctx.errors`. Default builds are byte-for-byte
  unaffected; flipping the flag is the "run it and measure" switch.

Landed in `driver.spl`:
- `run_typecheck_warn_pass(hir_modules)` — runs `HmInferContext.infer_module` +
  `check_module_visibility` per module, returns formatted `[text]` diagnostics.
- `lower_and_check_impl` calls it (log-only) when `SIMPLE_TYPECHECK_WARN=1`.

This mirrors the existing driver env-flag conventions (`SIMPLE_STUB_HIR`,
`SIMPLE_BOOTSTRAP_SKIP_MONO`, `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE`).

## 3. Phased burndown to fatal enablement

- **P0 — Wall.** Fix the stage4 wall so a trustworthy build exists (blocks all
  measurement). Until then everything below is wall-deferred.
- **P1 — Measure blast.** With a good build, set `SIMPLE_TYPECHECK_WARN=1` and build
  the compiler + a representative app set. Capture the log; bucket diagnostics by
  `TypeInferError` variant and by module. Deliverable: a diagnostic histogram appended
  here. First confirm the engine does not *crash* before trusting counts.
- **P2 — Triage.** Split diagnostics into (a) true type errors in source, (b) engine
  false positives (missing builtins, unsupported HIR constructs, incomplete unify
  cases). File (b) as engine bugs; fix (a) at source, module by module.
- **P3 — Visibility burndown.** Same loop for `[visibility Wxxxx]` warnings; most are
  expected to be intentional cross-module access needing `pub`/friend annotations.
- **P4 — Trait bounds.** Replace the `resolve_methods_with_solver` stub
  (`resolve.spl:712`) with real bound checking, driven by the `trait_solver` that
  `HmInferContext` already builds during inference — the natural integration point is
  to thread the post-inference `TraitSolver` into method resolution.
- **P5 — Flip to fatal.** Once a module's inference diagnostics are zero, route that
  module's `TypeInferError`s to `ctx.add_error` (fatal). Do this incrementally
  (allow-list of clean modules) rather than a global flip, so a regression is
  localized. Retire `type_check_impl`'s no-op and the effect_pass early-return.

## 4. Verification status

- Source-level confirmation of all four findings: **done** (citations above).
- Symbol/import/method-attachment checks for the warn-only wiring: **done**
  (`HmInferContext` exported by `type_infer/__init__.spl:5`; `infer_module` attached
  via `impl HmInferContext` in `inference_control.spl:23`, in the build closure via
  `inference.spl:33`; `check_module_visibility` exported by `35.semantics/__init__.spl:101`;
  `_format_type_infer_error` already imported by the driver).
- Full compiler rebuild to confirm the edit compiles and to count diagnostics:
  **WALL-DEFERRED** (seed miscompiles; bootstrap slow; deployed binary/LSP index the
  main checkout, not this worktree, and lint/fmt are themselves flagged broken in the
  same deep-recheck). No behavior change is possible with the flag unset, so the risk
  of the landed change to the default build is limited to a compile error in the added
  code, which source reasoning has minimized.
