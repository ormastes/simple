# `bin/simple test` double-executes unbound expression-statements inside `it` bodies (2026-08-18) — CONFIRMED, narrower than reported

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
