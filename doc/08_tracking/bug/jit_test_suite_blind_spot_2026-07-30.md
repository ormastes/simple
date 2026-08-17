# The spec suite is structurally blind to JIT-only defects (2026-07-30)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## 3. Corpus and results (run against the deployed `bin/simple`, 2026-07-30)

| Fixture | Pinned bug | Expected | Interpreter | JIT | Result |
|---|---|---|---|---|---|
| `chained_to_i64_twice.spl` | `reference_jit_chained_method_to_i64_returns_garbage.md` | `pw=480 ph=360` | correct | correct in every run observed by this lane (see §3a — **UNRESOLVED, contradicted by lane a894**, do not treat as fixed) | see §3a |
| `module_level_val_from_call.spl` | `reference_jit_module_level_val_from_function_call_reads_zero.md` | `X=42` | correct | wrong (`X=0`) | **Still open** — engines disagree, JIT wrong |
| `struct_field_compound_assign.spl` | `jit-struct-field-compound-assign-loads-zero-2026-07-27` | `n=7` | correct | wrong (`n=2`, i.e. `0+2`) | **Still open** — engines disagree, JIT wrong |
| `list_get_shifted.spl` | `reference-list-get-returns-value-shifted-left-3` | `idx=5 get=5` | correct | correct in every run observed by this lane (see §3a — **UNRESOLVED**, do not treat as fixed) | see §3a |

### 3a. UNRESOLVED cross-lane contradiction — do not mark these two bugs "fixed"

Lane a894 reported the *opposite* result on **the same deployed binary**:
`chained_to_i64_twice`'s exact repro producing identical garbage, exactly 32
apart, over 3 independent runs, explicitly cross-validated against the
154MB LLVM build. This lane's own results (10-15 runs, see below) are
directly contradictory. Per instruction, this was investigated rather than
either side being written off; the contradiction is **not fully resolved**,
and the corpus entries are marked UNRESOLVED rather than "fixed" until it
is.

**Hypotheses checked and ruled out by this lane, with evidence:**

1. **"Native-build spawns a worker on `bin/simple` regardless" (per
   instruction, checked first).** `strace -f -e trace=execve,clone,fork,vfork`
   on `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 bin/simple run
   repro.spl` shows exactly **one** `execve` (the top-level invocation) and
   a `clone()` with no subsequent `execve` in the child — i.e. a thread, not
   a subprocess exec'ing a different binary. `simple run`'s JIT path does
   not fork a worker. Ruled out for this invocation shape.
2. **`SIMPLE_EXECUTION_MODE=jit` silently resolving to the LLVM backend on
   this specific (LLVM-linked) binary, rather than Cranelift.** Read
   `ExecutionMode::parse_str` (`exec_core.rs:36-43`): any string other than
   `"interpret"`/`"interpreter"`/`"cranelift"`/`"llvm"` — including plain
   `"jit"` — falls through to `ExecutionMode::Jit`, which resolves to
   `JitBackend::Auto` (`exec_core.rs:807-809`). Read `JitBackend::auto_select`
   (`codegen/local_execution.rs:29-45`): on `target_pointer_width = "64"`
   (this host), it unconditionally returns `JitBackend::Cranelift` — no
   LLVM-availability check at all on 64-bit. Ruled out by direct code
   reading.
3. **Binary identity — confirmed, not assumed.** The exact binary invoked:
   `bin/release/x86_64-unknown-linux-gnu/simple`, `sha256:
   ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d`, 154,095,344
   bytes, `strings <bin> | grep -c "llvm::"` = **617** (matches the count
   the coordinator cited for the canonical LLVM build — an earlier `^llvm::`
   anchored grep by this lane wrongly reported 0 and was a false alarm from
   the anchor, not a real binary swap; unanchored count is 617). Hash
   re-checked twice, ~15 minutes apart, unchanged — the binary was stable
   for the duration of this lane's testing.
4. **ASLR.** `/proc/sys/kernel/randomize_va_space` = `2` (full
   randomization) — ASLR is on, so if the bug's mechanism is address-leak
   under a fixed structural offset (the coordinator's leading hypothesis:
   frame/spill-slot addresses, always 32 bytes apart because that's a fixed
   in-frame delta, with the *base* varying per-process under ASLR), an
   address leak would print a **different large wrong number each run**,
   not the same correct one. This lane's repeated runs (10 for
   `chained_to_i64_twice`, 3 for `list_get_shifted`, plus variants with an
   empty environment and a nested `/bin/sh -c` wrapper matching the
   harness's own invocation shape) all printed the exact correct values
   every time (`pw=480 ph=360`; `5 5` / `9 9` / `42 42`), never a large
   number. If ASLR-dependent address leakage were firing in this lane's
   process instances, literal-value ground truth would have surfaced it as
   "wrong, and different each time" — it did not. This does not rule out
   the address-leak mechanism for lane a894's environment; it does rule out
   "this lane's literal-value check is silently passing on leaked addresses
   by coincidence."
5. **Not explained:** why lane a894's environment differs from this lane's
   for `chained_to_i64_twice` specifically remains open. `list_get_shifted`
   is a *separately* documented, deterministic bug (`value << 3`, a fixed
   tag-encoding shift, not address-dependent) — the ASLR hypothesis does
   not apply to it at all, and this lane's non-reproduction of it is
   independently unexplained.

**Disposition:** the memory notes for both bugs are **not** being updated
to "fixed." Both corpus fixtures are left in the harness exactly as pinned
(literal-value ground truth), because for this specific investigation a
literal check turned out to be the *more* diagnostic choice (see point 4
above) — a purely structural check (e.g. "value is implausibly large") would
have been unable to distinguish "genuinely fixed" from "leaked address that
happens to be small" as cleanly. What *is* added, per the instruction to
write this up as a general finding: a secondary structural diagnostic in
the harness (§2) that classifies a wrong JIT value as
"address-shaped" (implausibly large in magnitude) versus "other," so a
future run that *does* reproduce garbage reports which known mechanism it
matches, without weakening the primary literal-value pass/fail check.
Reconciling the two lanes' results needs a same-session, same-process-tree
comparison (e.g. both lanes running back-to-back against a hash-pinned copy
of the binary saved to disk) that is outside what one lane can do alone —
flagged here for the next lane or the coordinator to arrange.

`sentinel_basic_arithmetic.spl` (regression guard, not a pinned bug):
expected `sum=30`, both engines correct, as expected.

Bottom line for this pass: 2 of 4 pinned bugs (`module_level_val_from_call`,
`struct_field_compound_assign`) reproduce exactly as documented — engines
disagree, JIT wrong, no ambiguity. The other 2
(`chained_to_i64_twice`, `list_get_shifted`) are **UNRESOLVED** per §3a
above — this lane could not reproduce them despite exhausting the checks
listed there, but a sibling lane reports the opposite on the same binary
hash, so they remain open in the memory notes, not closed.

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
- The "deployed `bin/simple`" is a moving target in a shared, multi-lane
  environment — it can be redeployed between one lane's test and another's,
  and both may correctly describe "the deployed binary" while meaning
  different bytes. Any cross-lane result on the deployed binary should
  record the exact `sha256sum` (and ideally `strings <bin> | grep -c
  llvm::` as a cheap sanity check) at the moment of testing, not just "the
  deployed binary," so a later reconciliation can confirm or rule out a
  binary swap as the explanation (§3a).

## Triage 2026-08-17 — PARTIALLY ADDRESSED (content evidence)

Classified against current source, not SHA ancestry.

The differential harness this report asked for now exists:
`scripts/check/check_jit_interpreter_differential.spl`, 271 lines, with a fixture
table under `test/fixtures/jit_differential/` (`chained_to_i64_twice.spl`,
`module_level_val_from_call.spl`, `struct_field_compound_assign.spl`, ...) and a
documented entry point `bin/simple run scripts/check/check_jit_interpreter_differential.spl`.
It cites this bug doc at line 22.

The ROOT condition is still live and still stated in that file at line 4: the
spec runner "unconditionally overwrites SIMPLE_EXECUTION_MODE to interpret", so
`bin/simple test` remains single-engine and JIT-only divergences stay invisible
to the suite itself. The harness is an out-of-band mitigation, not a fix to the
suite. Keep open, but rescope the title: the blind spot is now covered by an
opt-in harness that nothing gates on.

NOT proven here: whether the harness currently passes. Not executed.
