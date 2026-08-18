# `bin/simple test` double-executes unbound expression-statements inside `it` bodies (2026-08-18) — CONFIRMED, narrower than reported

## Update 2026-08-18: site localized (Rust seed), fix BLOCKED-ON-DEPLOY

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

CONFIRMED, not fixed. Confirms the claim made in passing by
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
