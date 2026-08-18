# `bin/simple test` double-executes unbound expression-statements inside `it` bodies (2026-08-18) — CONFIRMED, narrower than reported

## Update 2026-08-18 (later probe): does NOT reproduce now — root-cause question MOOT, status downgraded

**One targeted probe run.** Instrumented `exec_block_closure_into` in
`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` (the
`for node in nodes` loop, ~line 260) to print, per iteration, the loop index,
`nodes.len()`, and `std::mem::discriminant(node)` — exactly the index+len
data the prior update flagged as missing to distinguish "slice built with a
duplicate entry" from "loop re-enters the same index".

Built a debug seed with `CARGO_TARGET_DIR=/mnt/data/tmp/probe2_cargo_target
cargo build --release --bin simple` (foreground, exit status read directly,
not through a pipe: `EXIT:0`) from the **actual current working tree**
(HEAD `bc6f2599c59` plus the other in-flight uncommitted changes already
present in this shared worktree — see caveat below). Ran the exact minimal
repro from this doc (unbound `rt_file_append_text` call + `print` +
`expect(1).to_equal(1)` inside one `it`) three times against the instrumented
binary via `SIMPLE_BOOTSTRAP=1 <probe-binary> test <repro>.spl`.

**Raw trace (identical across 3 runs):**
```
PROBE2 idx=0 len=1 disc=Discriminant(64)   # describe-block's single stmt: the `it "...": <block>` call
PROBE2 idx=0 len=3 disc=Discriminant(64)   # it-body stmt 0: print "MARKER_PRINT"
PROBE2 idx=1 len=3 disc=Discriminant(64)   # it-body stmt 1: rt_file_append_text(...) — the previously-doubled call
PROBE2 idx=2 len=3 disc=Discriminant(64)   # it-body stmt 2: expect(1).to_equal(1)
```
`nodes.len()` is `3` for the `it` body and each of indices `0,1,2` appears
**exactly once** — no repeated index (refutes hypothesis (b), loop
re-entry) and no `len` larger than the source's 3 statements (refutes
hypothesis (a), a duplicated slice entry). Sidecar file
(`rt_file_append_text` target): **1 line** (`MARKER_APPEND` once) on every
one of 3 runs, not 2. `grep -c MARKER_PRINT`: **1**, not the original
`Results:`-line-consistent-but-doubled-sidecar pattern this doc opened with.

**Cross-check against the actually-deployed binary (no debug seed, no
instrumentation):** re-ran the identical repro through
`bin/release/x86_64-unknown-linux-gnu/simple` (`bin/simple`, the binary every
`bin/simple test` invocation in this environment actually uses) with a fresh
sidecar path. Same result: sidecar file **1 line**, `MARKER_PRINT` count
**1**, `Results: 1 total, 1 passed, 0 failed`. **The bug does not currently
reproduce on the deployed binary either.**

**Caveat — HEAD alone does not compile.** `git worktree add --detach
<scratch> HEAD` (HEAD = `60f3188fdd3`) plus the identical instrumentation
failed to build on its own: 4 errors (`E0432` unresolved import
`module_globals_generation`, `E0425` missing `report_globals_census`, `E0308`
type mismatch in `module_evaluator.rs:147`, `E0599` trait-bound failure in
`interpreter_sffi.rs:125`). This means `origin/main`'s current tip is
presently unbuildable from a clean checkout — a real, separate finding
(flagged below, not fixed here, out of this investigation's scope). The only
build that succeeded and that this probe's evidence rests on used the shared
worktree's actual current state: HEAD plus other sessions' in-flight
uncommitted fixes to `src/compiler_rust/compiler/src/interpreter/node_exec.rs`,
`interpreter/block_exec.rs`, `interpreter_helpers/patterns.rs`, and others
(pre-existing in this worktree before this investigation started, not
authored by this probe). Diffed the relevant hunks: the `node_exec.rs` change
is an unrelated `MODULE_GLOBALS` reentrant-borrow fix
(`cell.borrow_mut()` nested inside `cell.borrow_mut()` -> split into a
`.borrow()` check then a separate `.borrow_mut()`), not a double-execution
fix, and does not touch `exec_block_closure_into` or
`handle_method_call_with_self_update`'s call structure in a way that would
plausibly explain the non-reproduction. The **deployed `bin/simple` cross-check
above is independent of this caveat** (it did not use the debug seed or any
worktree at all), and it also failed to reproduce — so the non-reproduction is
not solely an artifact of building against a dirty tree.

**Verdict: neither hypothesis (a) nor (b) can be confirmed — the defect is
not currently observable to test against.** Either (i) it was already fixed by
one of the many other changes that have landed on `src/compiler_rust` since
this doc's original evidence was gathered earlier on 2026-08-18, or (ii) it is
sensitive to a precondition (build flags, execution mode, a specific prior
statement shape, timing) not captured by this repro and the earlier one. This
probe cannot distinguish (i) from (ii) — it only establishes that the exact
documented repro, run 4 times total across 2 independently-built binaries
(1 debug-instrumented, 1 the actual deployed production binary), produced the
**correct, non-doubled** result every time.

**New, separate, out-of-scope finding:** `origin/main` at `60f3188fdd3` fails
`cargo build`/`cargo check` on `src/compiler_rust` with 4 real compile errors
(see above) when built from a clean worktree with no other session's
uncommitted fixes applied. This contradicts the "seed must still compile"
pre-push guard's premise and should be filed/investigated separately — not
addressed here per this task's BLOCKED-ON-DEPLOY / investigation-only scope.

**Status downgraded:** CONFIRMED (as of the original 2026-08-18 evidence) ->
**NOT CURRENTLY REPRODUCIBLE** (as of this later probe, same day). Kept as
BLOCKED-ON-DEPLOY / open rather than closed, because non-reproduction under
one repro run is not proof of absence, and the original evidence (8-line
trace showing back-to-back re-entry) was concrete and specific enough to not
dismiss as an artifact. Whoever picks this up next should: (1) rerun the
exact original evidence-gathering steps verbatim before assuming a fix, (2)
if still non-reproducing, downgrade this doc's status further with a note
that it could not be reproduced twice, and (3) separately file the
`origin/main` HEAD compile-failure finding above, which is real and current
regardless of this bug's status.

## Update 2026-08-18 (earlier): site localized (Rust seed), fix BLOCKED-ON-DEPLOY

**Site:** `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`,
function `exec_block_closure_into`, the `Node::Expression(expr)` match arm
(~line 261-287, the block reached via `exec_block_value` /
`exec_block_closure` — the path `"it" | "slow_it" | "limited_it"` in
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs:820` uses to run an
`it` body's `Value::BlockClosure`).

**Causality evidence.** Built a debug seed
(`CARGO_TARGET_DIR=<scratch>/cargo_target cargo build --release --bin simple`,
exit 0) with two temporary `eprintln!` probes bracketing the
`handle_method_call_with_self_update(expr, ...)` call inside the
`Node::Expression` arm, printing `std::mem::discriminant(expr)` on entry and a
plain "done" on exit. Ran the exact minimal repro from this doc against the
instrumented binary directly (bypassing the deployed seed symlink):

Unbound-call repro (`print`; bare `rt_file_append_text(...)`;
`expect(1).to_equal(1)`) — 8 trace lines, correctly nested:
```
start Discriminant(18)   # outer describe-block statement: the `it "...": <block>` call
  start Discriminant(18) # it-body stmt 1: rt_file_append_text(...) call
  done
  start Discriminant(18) # it-body stmt 1 AGAIN — same discriminant, no intervening stmt
  done
  start Discriminant(20) # it-body stmt 2: expect(1).to_equal(1) (MethodCall)
  done
done
```
Sidecar file: 2 lines (`MARKER_APPEND` x2), `MARKER_PRINT` once — matches the
doc's original raw counts exactly.

Val-bound control (`val ok = rt_file_append_text(...)`; `expect(ok)...`) run
through the same instrumented binary — only 4 trace lines:
```
start Discriminant(18)   # outer describe-block statement (the `it` call)
  start Discriminant(20) # it-body stmt: expect(ok).to_equal(true) (MethodCall)
  done
done
```
Sidecar file: 1 line. The `val ok = ...` statement is a `Node::Let`, a
different code path in the same function (not the `Node::Expression` arm just
instrumented) and is not traced here at all — consistent with it running
exactly once.

**Conclusion.** Inside a single pass of `exec_block_closure_into`'s `for node
in nodes` loop over an `it` body's `Value::BlockClosure`, the
`Node::Expression` arm is entered and exited **twice in a row for the same
bare-call statement** before the loop proceeds to the next statement — while a
`Node::Let` (bound) statement and a `Node::Expression` whose expr is a
`MethodCall` (`expect(...).to_equal(...)`) are each entered exactly once. This
localizes the defect to either (a) the `nodes: &[Node]` slice for an `it`
body's `BlockClosure` literally containing the bare-call statement twice
(built somewhere upstream — parser or `Value::BlockClosure` construction for
`it "...": <indented block>`), or (b) the loop body re-invoking the same
iteration for that one node kind. Distinguishing (a) from (b) needs one more
probe (`nodes.len()` / node index printed alongside the discriminant) that
this investigation's budget did not reach — flagged as the next step below.

**Proposed patch (not applied — see fix decision):** once (a) vs (b) is
confirmed, either de-duplicate the `nodes` vector at whatever site
constructs the `it`-body `BlockClosure`, or (if (b)) remove the duplicate loop
iteration in `exec_block_closure_into`'s `Node::Expression` arm in
`block_execution.rs`. No code was changed to test this — the fix requires
locating the duplication's origin first, which is additional work beyond this
task's budget.

**Fix decision: BLOCKED-ON-DEPLOY, not fixed.** The site is in
`src/compiler_rust` (the Rust seed). The deployed `bin/simple` (used by every
`bin/simple test` invocation in this environment) is this same seed
(`bin/simple --version` prints the `WARNING: this Rust-built Simple binary is
a bootstrap seed only` banner) — a source fix here has no effect until the
seed is rebuilt and redeployed, which is Bootstrap Stage 3's blocker (see
`.claude/rules/bootstrap.md`). Per CLAUDE.md's "Default tooling = pure-Simple
self-hosted binary" and the seed-fix constraint noted in the task, no
compiler-side change was landed. All temporary `eprintln!` instrumentation was
reverted before committing; `git diff -- src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`
is empty.

## Status

NOT CURRENTLY REPRODUCIBLE (see "Update 2026-08-18 (later probe)" above — 4/4
runs across the debug seed and the deployed binary showed correct,
non-doubled execution). Originally CONFIRMED, not fixed, confirming the claim
made in passing by
`doc/08_tracking/test/sspec_binary_md_manual_status_2026-08-18.md` ("the
test-runner path executed the spec file's `it` bodies twice within one
invocation"), but the mechanism is **narrower** than "the whole `it` body runs
twice": only **unbound expression-statement calls** (a statement that is a
bare call whose return value is not assigned to anything) inside an `it` body
are evaluated twice. `print` statements and calls whose result is bound to a
`val`/`var` run exactly once. Filed as a standalone bug per that doc's
"filing a dedicated bug ... is separate follow-up work" note.

## Minimal reproduce

```
extern fn rt_file_append_text(path: text, content: text) -> bool

describe "double execution repro":
    it "appends one marker line and prints one marker":
        print "MARKER_PRINT"
        rt_file_append_text("<sidecar path>", "MARKER_APPEND\n")
        expect(1).to_equal(1)
```

Run: `bin/simple test <path>` (binary in use: the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`, a Rust seed spawning the same
seed binary as the test child — confirmed via the `WARNING: this Rust-built
Simple binary is a bootstrap seed only` banner and one `child binary: ...`
line in the log, i.e. exactly one child process, not two).

Raw counts:
- `MARKER_PRINT` in captured stdout: **1** occurrence (one line, `grep -c` = 1)
- Sidecar file lines (`rt_file_append_text` calls): **2** lines
  (`MARKER_APPEND` appears twice)
- `SPEC FILE VERDICT ... executed=1 passed=1 failed=0`
- `Results: 1 total, 1 passed, 0 failed`

So the runner reports **1 executed example**, but the unbound extern call
inside that one example's body ran **twice**, while the `print` statement in
the same body ran **once**.

### Control 1 — bound result, same `it` body shape

```
val ok = rt_file_append_text("<sidecar path>", "MARKER2\n")
expect(ok).to_equal(true)
```
Sidecar file: **1** line. `Results: 1 total, 1 passed, 0 failed`.
Binding the call's return value to a `val` makes it execute once.

### Control 2 — same unbound call, but at top level (`fn main()`, `bin/simple run`, not inside `it`)

```
fn main():
    rt_file_append_text("<sidecar path>", "TOPLEVEL\n")
```
Sidecar file: **1** line. So the double-evaluation is not a general
interpreter behavior for unbound expression-statements — it is specific to
statements evaluated inside an `it` body under `bin/simple test`.

## Site

Not conclusively localized within this investigation's budget. `it`/`describe`
are handled as built-in syntax (no `use` needed, no library `fn it(...)`/`fn
describe(...)` found under `src/lib/**/spipe.spl`), and no `"it"`/`ItBlock`
keyword handling was found via grep under `src/compiler/95.interp` — grammar
handling is presumably elsewhere in the frontend/desugar pipeline
(`src/compiler/10.frontend/parser/test_analyzer.spl` is the only frontend hit
for the `"it"` token but was not read in depth). The evidence narrows the
search space usefully for a follow-up: whatever evaluates an `it` body
statement-by-statement treats **unbound expression-statement calls**
differently from **bound-result calls** and from the built-in `print`
statement — consistent with a coverage/unused-result analysis pass that
re-evaluates (rather than merely re-inspects) an expression statement's
return value when nothing consumes it.

## Impact

- Every spec whose `it` body contains a bare (unbound) call with a side
  effect — file/socket/DB writes, counters, sidecar evidence appends, mutation
  of external state via an unbound extern or method call used only for its
  side effect — runs that side effect **twice** per reported example. This is
  exactly the `spipe-docgen` evidence-sidecar failure mode that surfaced this
  bug: an append-only writer called as a bare statement doubles every
  evidence block in the generated manual.
- Specs that only bind results (`val x = f(...)`) or only assert
  (`expect(...)`) are **not** affected in outcome, only in count semantics if
  they happen to also contain unbound calls.
- Cost: doubles wall time and resource use for any unbound side-effecting
  call, though at spec-body granularity, not whole-body granularity — no
  isolated timing comparison was run (the effect is per-statement, not
  per-file, so a single before/after wall-clock number would not isolate it
  meaningfully without also fixing the call site).

## What a fix should assert (per binary_runtime_hardening plan's "fix test standard")

- **Reproduce spec**: the exact repro above, asserting the sidecar file has
  exactly 1 line and `MARKER_PRINT` appears exactly once after the fix.
- **Similar cases**:
  - nested `describe` blocks, unbound call inside the inner `it`
  - multiple `it`s in one `describe`, each with its own unbound call — each
    sidecar line appears exactly once per `it`, not accumulated across `it`s
  - a `skip`/pending `it` — its unbound call must not execute at all (0
    lines), to guard against a fix that accidentally makes skipped bodies run
  - the bound-`val` control (Control 1 above) must remain at exactly 1 line
    (regression guard against overcorrecting to zero executions)

## Fix decision

**Not fixed.** The call site was not conclusively located (see "Site" above),
`it`/`describe` handling is load-bearing infra used by ~19,500 tracked
`*_spec.spl` files, and CLAUDE.md/testing rules require any change here to be
verified against a broad regression sweep. Per the task's own guidance,
leaving this as a bug doc rather than attempting an uncontained fix is the
correct outcome. Suggested next step for whoever picks this up: instrument
the interpreter's expression-statement evaluation (or the `it`-body desugar)
to print a call-site trace, rerun the minimal repro, and diff against the
bound-`val` control to find exactly where the second evaluation is
introduced.
