# The spec suite is structurally blind to JIT-only defects (2026-07-30)

Motivation: `SIMPLE_EXECUTION_MODE=jit` is the default engine for plain
`simple run`, but `bin/simple test` unconditionally forces interpreter mode
for every child spec (proved with a direct code citation in
`doc/08_tracking/bug/jit_strict_coverage_gap_2026-07-30.md` §4a:
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:86`,
`env_set("SIMPLE_EXECUTION_MODE", "interpret")`). This session alone found
several JIT-only defects by hand — all silent-wrong-answer, none crashing —
and the suite would report green through every one of them indefinitely.
This is the largest verification hole currently on record in this repo.

## 1. Why line 86 (and `test_runner_single.spl:168`) exists — investigated before touching anything

**The comment's stated reason:**

```
# Child `run <file>` must execute in interpreter mode to load BDD test
# intrinsics (`describe`/`it`/`expect`). Without this, `simple test
# --mode=interpreter` can still dispatch a child in compile mode,
# producing parse errors + zero evidence.
```

Landed `8d2a12e6270` (2026-07-25), "test: force interpreter execution mode
in test runners". The commit body has no further explanation beyond this
comment.

**Timeline check:** the HIR-level BDD lowering that turns `describe`/
`context`/`it`/`expect` into real `rt_bdd_*` runtime calls
(`try_lower_bdd_statement`, `hir/lower/stmt_lowering.rs:1897`, dispatching
to registered JIT runtime symbols `rt_bdd_describe_start_rv` /
`rt_bdd_it_start_rv` / `rt_bdd_describe_end` — confirmed present in
`codegen/runtime_sffi.rs` and implemented in `runtime/src/value/bdd_sffi.rs`)
was introduced **2026-07-01**, three weeks *before* the interpret-mode fix
landed. So JIT-side BDD support already existed when the fix was written —
the fix's own comment describing BDD intrinsics as unavailable outside
interpret mode does not match what the HIR lowerer had already been doing
for three weeks.

**Direct empirical re-test (PROVED, not inferred), today, both a fresh Rust
seed build and the actual deployed `bin/simple` (154MB, LLVM-linked,
redeployed today):**

- A trivial `describe`/`it`/`expect` spec, run directly via `simple run`
  under `SIMPLE_EXECUTION_MODE=jit`, `=interpret`, and fully unset: **all
  three produce identical, correct output** (`2 examples, 1 failure`, same
  pass/fail lines, same formatting).
- A richer spec (nested `context`, `before_each`/`after_each`, array and
  text matchers) likewise produces **identical output under JIT and
  interpret** — no parse error, no "zero evidence," in either engine.
- `build_coverage_wrapper` is a no-op unless `options.coverage` is set (the
  default `simple test` invocation), so the wrapping the runner actually
  applies in the common case does not explain a JIT-only parse failure
  either.
- A genuinely separate, real bug was found while reading this code, unrelated
  to which engine executes the file: `preprocess_infix_matchers_only`'s own
  docstring states legacy word-infix `expect X to_equal Y` lines are
  silently dropped by the `run`/interpreter path specifically — "a falsy
  call subject false-REDs... any other subject silently false-GREENs." This
  is a real defect but it is about matcher **syntax form**, not about which
  **engine** compiles the file, and it affects the interpreter path too — it
  does not explain why JIT specifically needed to be excluded.

**Conclusion — honest, bounded:** the specific failure mode the line-86
comment describes (BDD intrinsics unavailable, "parse errors + zero
evidence") does **not** reproduce today on the constructs tested. This
suggests the original bug was either already fixed independently by the
time the BDD HIR lowering landed, or was narrower than the whole-runner
scope the fix defensively applied. **This is not proof the guard is safe to
remove everywhere.** Not tested: the full ~2,500-file spec corpus,
fork-mode execution, coverage-mode execution, or the actual self-hosted
bootstrap rebuild+full-suite run that would be required to validate a
runner change with full confidence — that rebuild is expensive and
"no bootstrap unless essential" applies. **Line 86 was not touched.**
Per the task's explicit permission to say "the runner genuinely cannot host
a JIT lane [without more validation than is in budget]" and propose the
smallest safe alternative, this pass built a **separate, `simple
run`-based differential harness** instead (§2) — it needs no runner change,
no bootstrap rebuild, and no risk to the existing suite.

**Ruled out as a shortcut:** a sibling lane found `SIMPLE_TEST_RUNNER_RUST=1`
appears to "revive" an alternate `simple test` path, but further
investigation by that lane found it short-circuits to the seed's baked-in
Rust runner *before* Simple-app dispatch — it is structurally blind to
`.spl` edits (reverting a `src/compiler` change produced byte-identical
output under it). Plain `bin/simple test` was confirmed to work without it.
This harness does not use that override anywhere.

## 2. The differential harness

`scripts/check/check_jit_interpreter_differential.spl` — a plain `fn
main()` Simple program (not a `_spec.spl`, so the BDD test runner's static
spec discovery never picks it up and it is never routed through the
interpret-mode-forcing dispatch described above). Run directly:

```
SIMPLE_BIN=/path/to/bin/simple bin/simple run scripts/check/check_jit_interpreter_differential.spl
```

For each fixture in a small pinned corpus, it shells out to `simple run`
twice — once under `SIMPLE_EXECUTION_MODE=interpret`, once under
`SIMPLE_EXECUTION_MODE=jit` — and compares both outputs against a
hand-pinned ground-truth `expected` string (from the original bug reports)
and against each other. Disagreement between engines is reported
regardless; only a fixture's documented `known_good` engine(s) failing to
match ground truth counts as an "unexpected failure" (exit code = count of
those). A still-open, already-known JIT bug reproducing again is *expected*
and does not fail the run — the point is to catch **new** regressions and
to notice when a **pinned bug disappears** (which happened twice this pass,
see §3).

## 3. Corpus and results (PROVED, run against the deployed `bin/simple`, 2026-07-30)

| Fixture | Pinned bug | Expected | Interpreter | JIT | Result |
|---|---|---|---|---|---|
| `chained_to_i64_twice.spl` | `reference_jit_chained_method_to_i64_returns_garbage.md` | `pw=480 ph=360` | correct | **correct** (4/4 repeat runs) | **Bug no longer reproduces** — both engines agree and match ground truth |
| `module_level_val_from_call.spl` | `reference_jit_module_level_val_from_function_call_reads_zero.md` | `X=42` | correct | wrong (`X=0`) | **Still open** — engines disagree, JIT wrong |
| `struct_field_compound_assign.spl` | `jit-struct-field-compound-assign-loads-zero-2026-07-27` | `n=7` | correct | wrong (`n=2`, i.e. `0+2`) | **Still open** — engines disagree, JIT wrong |
| `list_get_shifted.spl` | `reference-list-get-returns-value-shifted-left-3` | `idx=5 get=5` | correct | **correct** (4/4 repeat runs) | **Bug no longer reproduces** — both engines agree and match ground truth |
| `sentinel_basic_arithmetic.spl` | (regression guard, not a pinned bug) | `sum=30` | correct | correct | OK, both correct, as expected |

Two of the four pinned bugs (`chained_to_i64_twice`, `list_get_shifted`) no
longer reproduce on the currently deployed binary (154MB, LLVM-linked,
redeployed today ~09:08) — re-verified 4 independent runs each, consistent
every time. **This is worth flagging to the owners of those two memory
notes/bug docs**: either the LLVM redeploy incidentally fixed them, or an
unrelated lane fixed them today. This harness does not attempt to root-cause
that — it only reports the current, empirically observed state. The other
two (`module_level_val_from_call`, `struct_field_compound_assign`) remain
open exactly as documented.

## 4. Non-vacuity proof — reverse control (per explicit instruction, done twice: once for this harness, once already done for the JIT-strict work)

Deliberately corrupted `sentinel_basic_arithmetic`'s pinned `expected` value
from `"sum=30"` to `"sum=99999"` (a value the program can never produce) and
re-ran:

```
[sentinel_basic_arithmetic] expected=sum=99999
  interpret: ok=false agree_with_jit=true
  jit:       ok=false
  status: REGRESSION
---
unexpected failures (regressions): 1
```
Harness exit code: **1**. Restored the correct value and re-ran:
```
status: OK (both correct)
---
unexpected failures (regressions): 0
```
Harness exit code: **0**. The harness is confirmed to actually observe the
programs under test rather than reporting green unconditionally.

## 5. What this harness is and is not

- It is a hand-run diagnostic script, not wired into `bin/simple test` or
  any CI gate — landing it does not change default `simple test` behavior
  at all (per the "don't weaken anything to make it pass" constraint, and
  because line 86 was deliberately not touched, see §1).
- It is a small, seeded corpus (4 pinned bugs + 1 sentinel), not a general
  JIT/interpreter fuzzer. Extending it is straightforward: add a fixture
  file to `test/fixtures/jit_differential/` and an entry to `fixtures()`
  with a pinned `expected` value and `known_good` engine(s).
- Both engines are independently untrustworthy (this session found bugs on
  each side); the harness's ground truth is the hand-pinned `expected`
  value from the original bug report, not either engine's own output.
