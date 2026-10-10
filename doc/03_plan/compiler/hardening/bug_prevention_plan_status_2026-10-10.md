# Compiler robustness / bug-prevention plan — status (2026-10-10)

Scope: the priority cut of the four 2026-10-09 robustness plans (recurrent-bugs
gap and hardening plan v2, robustness update plan v2, robustness final plan v2,
bug-prevention final plan), ordered by which current bootstrap blocker each item
prevents. Target branch: `release/1.0`. This file records status only; each item's
design lives with its guide under `doc/07_guide/compiler/robustness/` once landed.

Status words: **landed** (on `release/1.0`, PR given), **approved** (reviewed,
in the landing queue), **in review**, **rework** (review found a defect),
**in progress** (agent implementing), **parked**.

## Rules every item follows

- New diagnostics are warn-first with a level switch (`error|warning|off`); `off`
  skips the work, not only the output. Nothing may turn a module of the compiler's
  own closure that compiles today into a hard error.
- "Fully implemented" = implementation + acceptance sspec (must-pass and must-fail,
  red without the implementation) + a short guide + a status note.
- Every change is reviewed before landing and lands as its own PR.
- Workarounds are tagged `# WORKAROUND(stage2:<bug-key>, BUG-<id>)`, one commit and
  one bug record per bug-key, semantically neutral only.

## Item status

| # | Plan id | Feature | Status |
|---|---|---|---|
| 1 | 2a | Bare enum variants resolved by the match subject's type | Core fix **landed** by another session (declared-enum pattern handling). Remainder (wrong-enum warning, untyped-parameter rule, `Some`/`Ok`/`Err` slots) rebased, **in review** |
| 2 | 1a | No `Infer`/`Unknown` type survives into MIR silently | **in progress** |
| 3 | 11a | Type-only module is a valid export origin | **landed** #2876 |
| 4 | 13a | Post-monomorphization verifier (`E-MONO-*`) | **approved**, landing |
| 5 | 12a | One module-resolution order + conformance spec | **parked** — needs a full bootstrap run and an owner decision on the order (recommended: the seed's `__init__`-first) |
| 6 | 9a | MIR typed-cast / store / arity verifier | **rework** done after a blocking review (two lowering diagnostics were fatal on four non-driver routes); **in review** again. Its independent bug fix (vectorize prologue arity) **landed** #2873 |
| 7 | 6a/6b | `non-optional == nil` is not a sentinel compare; Optional is always boxed-or-nil | Series **approved**; pre-landing audit commits **in review** |
| 8 | 7a/7b | Written `Any` ≠ parser fallback; `Any` warn rules | 7a **landed** #2829 (other session); 7b **in progress** |
| 9 | 10a | Per-module internal-error boundary in the driver worker | **in progress** |
| 10 | 3a | Match-guard count invariant + guard parity spec | **in progress** (extends the verifier branch of item 6) |
| 11 | 8a/8b | HIR cache integrity self-check + cold==warm gate | **approved**; waits for the HIR codec fix to land, plus a nits commit (direct `rt_*` sites, temp leaks) |
| 12 | 12b | Seed ↔ stage-2 differential corpus gate | **in progress** |
| 13 | 15a | Non-vacuity: spec assertion counting; compile-lane receipts; shell exit-code hygiene | Assertion counting **approved** (with item 11); receipts + hygiene **in progress** |
| 14 | 2b/1b | Warn-first frontend lints (variant-shadowing binding, nil-compare, fallback use) | **approved**, landing |
| 15 | 14a | Stale-snapshot rewind guard in required PR gates | **landed** before this plan (2026-09-23) |
| 16 | 5a/16a/18/20 | Statics typed by visit order; memory/disk policy; small items | Memory cap policy **landed** #2826; the rest **in progress** |

## Fixes landed on `release/1.0` on 2026-10-10 from this lane

| PR | Change |
|---|---|
| #2866 | MIR: keep the struct type of locals bound from imported functions returning foreign structs |
| #2873 | mir_opt: vectorize prologue passes all arguments to the alignment-check builder |
| #2875 | codegen: seed-parity text casts via `ConvertCall`; LLVM codegen errors recorded fail-closed |
| #2876 | Type-only modules are object-less, not an export-origin error |

Ready or close: mono symbol-key fix for the `comparing string with integer`
regression introduced by `fb05765b78b`; HIR codec fix (cache never hit under
stage 2); post-mono verifier; frontend lints; lint crash fix (lint must run in
interpreter mode); export-origin prune (defence in depth behind `f09866fde9e`).

## Bootstrap state

- **Phase 3** (stage-2 compiler compiling the compiler, 1160 modules): passed HIR
  for the first time; stopped in monomorphization on 36 × `E-MONO-032` — explicit
  call type arguments `f<T>(...)` dropped before mono (35 sites in
  `80.driver/cache/cas_batch_transaction.spl`, 1 in
  `35.semantics/enum_contract/hir_match_coverage.spl`). `fb05765b78b` on release
  is reported to address the parser side; not yet verified on a rebuilt stage 2.
  MIR, codegen and link have not been reached on the full closure.
- **Phase 4** (stage-2 building the full CLI, LLVM and Cranelift): in HIR; the
  `invalid export origin` class is fixed on release (`f09866fde9e`).
- **Next step:** rebuild stage 2 from the release tip (it now carries the real
  fixes for bare variants, export origins, text casts and explicit type
  arguments) and re-run phase 3 without source workarounds.

## Open defects found by review, not yet fixed on release

- Two generic specs red on release: `generic_walker_fn_param_abi_spec`,
  `visitor_fn_param_ctx_inference_spec` — after the symbol-key fix, an older
  failure remains (`substitute_type` returning nil against a non-optional return).
- Generic struct field typed by a type parameter: per-instance field types leak
  across functions and three shapes silently emit integer arithmetic on handles
  (fix `e6a135b3296` blocked in review).
- Native builtin lowerings: numeric `abs/min/max` hook can hijack a user-defined
  method of the same name (blocked in review).
- `bug-add` is not available in the current seed, so new bug records are files
  under `doc/08_tracking/bug/` without a `bug_db.sdn` row.

## Owner decisions pending

1. Module-resolution order for item 5 (recommended: the seed's).
2. Keep tracking `bin/simple.exe` or untrack it (default taken: keep, refreshed).
3. Which verifier rules are promoted from warning to error, and when (requires a
   full phase 3/4 run with the verifiers on).
