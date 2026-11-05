# Core interpreter: hard iteration caps on `while` (1,000,000, errors) and range `for` (1,000,001, SILENT stop)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-28  **Status:** OPEN  **Area:** `src/compiler/10.frontend/core/interpreter/eval.spl`
**Found by:** perf_interp profiling lane (release/2026-08-27 tip `bb87306b64c`)

## Defect

- `eval.spl:810` `eval_while_expr`: `val max_iterations: i64 = 1000000`; on reaching it the loop
  stops and `eval_set_error("while loop exceeded maximum iterations")` fires. A legitimate
  `while i < 2_000_000` program is a runtime ERROR.
- `eval.spl:741` `eval_for_expr` (range form): `while _range_iter < 1000001:` — the loop simply
  ends after 1,000,001 iterations with NO error, so `for i in 0..2_000_000: acc += i` returns a
  wrong result silently.

Both caps are unconditional (no env/flag), and they differ from each other and from the Rust
seed (no cap). A 1M-step loop is ~1 s of work in an interpreter; this is a feature limit that
will surface as a wrong answer, not a diagnostic, in the `for` case.

## Reproduce (once a pure-Simple binary can drive `core_interpret`)

```
fn main() -> i64:
    var acc: i64 = 0
    for i in 0..1500000:
        acc = acc + 1
    print "{acc}"     # core interpreter prints 1000001, expected 1500000
    0
```

## Fix direction

Make the cap opt-in (an execution-limit knob such as the existing `--execution-limit` CLI option
in `src/app/run/main.spl:124`), and make the range-`for` path report an error like `while` does
instead of truncating silently. Not changed in the perf lane (feature-affecting).

## Status update 2026-11-05 — partial fix on `work/seed-interp-fixes-20261105`

Re-triaged on the release/1.0.0-based branch; line numbers shifted and the live
path changed since 2026-08-28:

- Current cap sites: `eval.spl` `eval_while_expr` (loud 1,000,000, unchanged);
  `eval.spl` `eval_for_expr` range arm (silent 1,000,001); `eval.spl`
  `eval_range` (silent 10,001-element array truncation). The statement-form
  `eval_stmts.spl:455` (`eval_stmt_for`) and the list-comprehension arm in
  `_EvalOps/access_literal_assign_eval.spl:1030` carry the same silent
  1,000,001 pattern — outside the fixed file's ownership, still open.
- Live path: through `core_interpret`, `for i in 0..N:` evaluates the range via
  `eval_range` (eager array, "Range creates an array of integers for now"), so
  the observed silent wrong answer was the 10,001-element truncation, not the
  doc's predicted 1000001. Reproduced: `for i in 0..1500000: acc += 1` returned
  `acc = 10001` with NO error (before fix).

Chosen semantics: **complete correctly** for the range paths (not loud). A
range-for is bounded by the range end by construction (it cannot
infinite-loop), and the Rust seed has no cap, so truncation was never
protecting anything there — it only produced wrong answers. The `while` cap is
left as-is: it is loud, pre-existing, and guards genuinely unbounded loops;
making it opt-in (`--execution-limit`) remains open per the fix direction.

Changed in `src/compiler/10.frontend/core/interpreter/eval.spl`:
- `eval_for_expr` range arm: removed the `while _range_iter < 1000001` silent
  cap; loop now runs `while current <= limit` with the same
  inclusive/exclusive break semantics.
- `eval_range`: removed the 10,001-element silent cap; materializes the full
  range array.

Verification (seed binary `/private/tmp/rel100-cargo-a/release/simple test`,
run from the worktree root; specs execute the pure-Simple interpreter through
`core_interpret`):
- RED before fix: `range_for_no_silent_iteration_cap_spec.spl` 3 failures,
  `expected 10001 to equal 1500000` with no interpreter error (silent wrong
  answer demonstrated).
- GREEN after fix: same spec 4/4 PASS (exclusive range-for 0..20000 → 20000,
  inclusive 0..=20000 → 20001, short-loop control → 10, range array
  `0..12000` → len 12000). Fixtures were resized from the doc's 1.5M to
  20,001 iterations because the spec host itself is interpreted; the
  multi-million-iteration run did not finish in 5 minutes — a perf note, not a
  correctness gap (a 1.5M-element eager range array is the documented
  "array for now" design).
- Regression, all PASS: `while_body_scope_spec.spl` 6/6 (while path unchanged),
  `eval_spec.spl` 3/3, `eval_clear_warnings_spec.spl` 1/1,
  `short_circuit_eval_spec.spl` 9/9, `match_expr_binding_scope_spec.spl` 6/6,
  `env_scope_slot_reuse_spec.spl` 7/7.
- Seed counterpart checked: Rust seed runs `for i in 0..20000` → 20000 with no
  cap (grep of `src/compiler_rust` finds no interpreter loop cap), confirming
  the pure-Simple caps were pure-Simple-only behavior.

Still open (outside the owned file): the statement-form 1,000,001 silent cap in
`eval_stmts.spl:455` `eval_stmt_for`, the same pattern in
`_EvalOps/access_literal_assign_eval.spl:1030`, and the while-cap opt-in
(`--execution-limit`) feature. Evidence spec:
`test/01_unit/compiler_core/interpreter/range_for_no_silent_iteration_cap_spec.spl`.

