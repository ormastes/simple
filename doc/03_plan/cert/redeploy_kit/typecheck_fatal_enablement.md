# Redeploy Kit: Type-Checker Fatal Enablement

Closes the five tool-qualification `known_defects` that are *silent accepts of a
bad program* (TOR-FM-02): `arity_too_many`, `arity_too_few`, `arg_type_mismatch`
(the memory-safety one — a `text` pointer reinterpreted as `i64`),
`undefined_type_annotation`, `nonexhaustive_match`.

Status: **Phase A wiring implemented (redeploy-pending). Phases B/C designed only.**

> **2026-07-19 current-tree correction:** the Phase A implementation described
> below is absent from the authoritative source. `src/compiler` has no
> `SIMPLE_TYPECHECK_FATAL` or `run_typecheck_fatal_pass`; only warn-only
> `SIMPLE_TYPECHECK_WARN` remains. Treat the implementation and verification
> claims below as historical design evidence until the fatal pass is restored,
> source-reviewed, and rebuilt.

Parent plan: `doc/03_plan/compiler/type_system/typecheck_burndown.md`
(this is the concrete "P5 — flip to fatal", staged and gated).

## 1. Reproduction (deployed, frozen binary — 2026-07-06)

`bin/release/x86_64-unknown-linux-gnu/simple run <file>`:

| Repro | Deployed behavior | Should be |
|---|---|---|
| `arity_too_many.spl` (`add(1,2,3)`) | prints `3`, exit 0 | rejected |
| `arity_too_few.spl` (`add(1)`) | prints `1`, exit 0 | rejected |
| `arg_type_mismatch.spl` (`add("x",2)`) | prints `3878859172451` (raw text pointer as i64), exit 0 | rejected — **memory safety** |
| `undefined_type_annotation.spl` (`val x: Nonexistent`) | logs `HIR lowering error: Unknown type: Nonexistent`, falls back to interpreter, prints `5`, exit 0 | rejected |
| `nonexhaustive_match.spl` (`match e: E.A: 1`, call `f(E.B)`) | prints `0`, exit 0 | rejected |

All five reproduced. The `arg_type_mismatch` output is a live type/memory-safety
hole: the argument's heap text pointer is passed straight into an `i64` slot.

## 2. Root cause

The Phase-3 semantic layer is dormant (see burndown §1). A warn-only pass exists
behind `SIMPLE_TYPECHECK_WARN=1` (`driver.spl` `run_typecheck_warn_pass`, commit
a61d6971) that runs `HmInferContext.infer_module` + `check_module_visibility` and
only *logs*. Nothing routes those diagnostics to `ctx.errors`, so no program is
ever rejected on a type error. That warn wiring is itself frozen in the deployed
binary, so today even the flag warns nothing.

The engine's own logic is capable of catching the arity + arg-type classes
(source-traced, §4). It is the *wiring to fatal* that is missing.

## 3. Phased design (blast-radius-aware)

The whole reason the pass is warn-only is that the HM engine has never run over
the full ~993-module set; making *all* its diagnostics fatal, unmeasured, would
very likely reject code that compiles today and break the build. So enablement is
staged and each stage is gated by a flag that defaults OFF — the default build
stays byte-for-byte identical until a stage is proven safe on a real build.

- **Phase A — arity + argument-type fatal (memory-safety first). IMPLEMENTED.**
  New flag `SIMPLE_TYPECHECK_FATAL=1`. When set, `lower_and_check_impl` runs
  `run_typecheck_fatal_pass` and pushes each `TypeInferError` into `ctx.errors`,
  so the program is rejected. *Only* type-inference errors are made fatal here;
  visibility warnings are deliberately excluded (they are Phase P3 of the
  burndown and are mostly intentional cross-module access). This targets exactly
  the three unsound-accept classes that read raw memory as a typed value.
  - Blast-radius plan: with a clean redeployed build, run
    `SIMPLE_TYPECHECK_FATAL=1` over (a) the tool-qual corpus — the three repros
    must reject, the `negative/` set must still reject, and the `positive/` set
    must still *compile*; then (b) the compiler + a representative app set, and
    bucket any new rejections. If (b) is noisy, do not global-flip: gate fatal by
    a per-module allow-list (burndown P5) seeded with the corpus modules and grow
    it as modules reach zero diagnostics. The flag stays the master off-switch.

- **Phase B — unknown type annotation fatal.** `val x: Nonexistent` is already
  detected at HIR lowering (`HIR lowering error: Unknown type: Nonexistent`) but
  the JIT path swallows it and falls back to the interpreter, which ignores the
  annotation. Fix: make the lowering "unknown type" `Result` error propagate to
  `ctx.errors` on the check/native path instead of being demoted to an INFO log +
  interpreter fallback. This is a *different mechanism* than the HM engine and is
  scoped separately. (Phase A *may* incidentally catch it if the bad annotation
  survives lowering as a `Named` type and `unify(i64, Named)` fails — treat as
  unverified until measured.)

- **Phase C — non-exhaustive match fatal.** The HM engine does no exhaustiveness
  analysis. A checker exists but is unwired: `check_match_exhaustiveness`
  (`src/compiler/35.semantics/lint/match_exhaustiveness.spl`, exported, zero
  pipeline callers). Fix: wire it into the driver and, once its warn-measured
  output is clean, route its warnings to `ctx.errors` under the same fatal gate.
  It operates on AST decl indices (a different data model from HIR), so it is a
  larger, independently-verified change — hence its own phase.

Ordering rationale: A first because arity + arg-type are the memory-safety
classes (garbage/pointer-as-int) and are already fully caught by the engine, so
A is the highest safety-value, lowest-new-code step.

## 4. Why Phase A rejects the three targets (source trace)

- **Call inference** (`30.types/type_infer/inference_expr.spl:411` `case Call`):
  synthesizes the callee to `Function(param_types, ret, effects)`, then infers
  each argument. When the expected param type is known it uses
  `InferMode.Check(expected_param)` (line 439). Finally it builds
  `Function(arg_types, ret_var, [])` from the *actual* args and
  `unify`s it against the callee type.
- **`unify` for functions** (`30.types/type_infer/core.spl:113`):
  `case (Function(p1,r1,_), Function(p2,r2,_)) if p1.len() == p2.len()` — the
  guard requires equal arity; unequal arity falls through to
  `case _ : Err(TypeInferError.Mismatch)` (line 216). ⇒ `arity_too_many` /
  `arity_too_few` produce a `Mismatch`.
- **arg-type**: for `add("x", 2)`, arg 0 is checked in `Check(i64)` mode, driving
  `unify(text, i64)` → no matching case → `Mismatch` (line 216). ⇒
  `arg_type_mismatch` produces a `Mismatch`.
- **Error collection**: `infer_function` (`inference_control.spl:545`) funnels any
  `Err` from `infer_block` into `self.error(e)`, so it lands in `ictx.errors`,
  which `run_typecheck_fatal_pass` reads and pushes to `ctx.errors`.

Caveat (honest): `infer_module` (`inference_control.spl:594`) infers functions in
`module.functions.values()` order and binds each function's scheme at the *end*
of `infer_function`, with no signature pre-pass. In these repros the callee
(`add`) is defined before `main`, so its scheme is bound before `main` is
inferred; a forward reference could miss. Not a concern for the corpus, but a
signature pre-pass is a natural robustness follow-up before global fatal.

## 5. Implementation (this change)

- `src/compiler/80.driver/driver.spl`
  - `lower_and_check_impl`: after the existing `SIMPLE_TYPECHECK_WARN` block, add
    a `SIMPLE_TYPECHECK_FATAL == "1"` block that calls `run_typecheck_fatal_pass`
    and pushes each returned diagnostic to `self.ctx.errors` (so
    `self.ctx.errors.len() == 0` becomes false → build/compile fails).
  - New `pub fn run_typecheck_fatal_pass(hir_modules) -> [text]`: mirrors
    `run_typecheck_warn_pass` but returns ONLY the `[typecheck]` HM diagnostics
    (no visibility), formatted via the already-imported `_format_type_infer_error`.

No other files changed. The default build is unaffected (flag defaults OFF).

## 6. Test plan

- Redeploy-pending reject kit: `test/cert/redeploy_pending/typecheck_fatal/`
  (five `reject_*.spl` byte-copies + README). NOT run by the normal suite.
  Post-redeploy acceptance: `SIMPLE_TYPECHECK_FATAL=1 simple run reject_*.spl`
  must exit non-zero with a `[typecheck]` diagnostic for the three Phase-A files;
  the two Phase-B/C files are documented as still-accepted by a Phase-A-only
  build.
- Regression guard (post-redeploy): with the flag ON, the tool-qual `positive/`
  corpus must still compile and the `negative/` corpus must still reject — proves
  Phase A added no false positives on the corpus before any wider rollout.

## 7. Verification status (ruthlessly honest)

- **Verified now (on the frozen deployed binary):**
  - All five defects reproduced (§1).
  - Source trace that the HM engine emits a `TypeInferError` for the three
    Phase-A classes (§4), and that `run_typecheck_fatal_pass` routes those into
    `ctx.errors` (§5).
  - `driver.spl` parses (lint reaches module-graph analysis; the only failure is
    the unrelated interpreter-mode `rt_cli_run_lint` limitation).
  - The five `reject_*.spl` are valid programs (they run today).
- **Verify-pending-redeploy (CANNOT be checked without a rebuild — the fix is in
  `src/compiler`, compiled into the frozen binary):**
  - That `SIMPLE_TYPECHECK_FATAL=1` actually rejects the three Phase-A repros.
  - The real blast radius over the compiler + app set.
  - Whether Phase A incidentally covers `undefined_type_annotation`.
  - Phases B and C are design-only; not implemented.

No claim is made that the fix "works" behaviorally — that requires the deferred
rebuild/redeploy.
