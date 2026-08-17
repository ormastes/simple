# `.?` truthy-check returns the unwrapped payload (not `true`) when passed directly as a `bool`-typed call argument

- **Date:** 2026-07-20
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Area:** interpreter evaluation of the `.?` operator (`.? over is_* predicates`
  is the documented idiom per `.claude/rules/language.md`), under
  `bin/simple test` (SSpec evaluator).

## Symptom

Given a helper `fn check(condition: bool): expect condition == true` and an
`Option<T>`-returning call, `check(opt_value.?)` fails with the *unwrapped
payload* printed as the actual value, not a boolean:

```
✗ handles save/load roundtrip with 100 bugs
  expected Bug(valid: true, ..., id: bug_9, ...) to equal true
✗ performs atomic read successfully
  expected test content to equal true
✗ handles multiple atomic appends
  expected start
line_0
...
  to equal true
```

In every case, `x.?` evaluated to the Some/payload value itself (a `Bug`
struct, a `text` string) rather than a plain `bool`, when `x.?` is passed
directly as a call argument to a `bool`-typed parameter (not stored in an
intermediate `val` first).

## Confirmed repro location

`test/02_integration/lib/.spipe_matchers_persistence_intensive_spec.spl`
(before the workaround below), e.g.:

```simple
fn check(condition: bool):
    expect condition == true

fn get_bug(id: text):
    if self.bugs.has(id):
        return Some(self.bugs[id])
    nil
...
val bug_result = loaded.get_bug("bug_{i}")
check(bug_result.?)   # FAILS: "expected Bug(...) to equal true"
```

`bug_result` is `Option<Bug>`. `bug_result.?` should reduce to `true`
(Some-case) but instead the call receives the raw `Bug` struct.

## Command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 40 bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/lib/.spipe_matchers_persistence_intensive_spec.spl --no-session-daemon
```
(prior to the workaround; 6 examples failed, all with this identical shape)

## Root-cause hypothesis

Same general family as the "Chained methods on erased receivers" runtime
limitation noted in `.claude/rules/language.md` ("chains fail only when a
link's receiver type is erased ... Workaround: intermediate typed `val`") and
the standing memory note on `.?` landmines (`.? on 0-i64→false`). Here the
receiver isn't erased by a dict/ANY lookup, but the `.?` result is being fed
directly into a function-call argument slot; the interpreter appears to skip
coercing `.?` to a `bool` in that position and instead forwards the
underlying Option payload. Not confirmed against source (`interpreter_method`
/ `interpreter_call` in `src/compiler_rust`) — flagged for a compiler-team
follow-up, out of scope for this test-triage pass per the campaign rules (no
Rust seed source fix attempted).

## Workaround applied (this pass)

Per the fix-guide's own sanctioned migration list (`.?` on a value ->
`!= nil`), rewrote every `check(<opt>.?)` / `check(not <opt>.?)` in the
affected spec to `check(<opt> != nil)` / `check(<opt> == nil)`, and one
`check(<text>.?)` (non-Option, checking a `file_read` result) to
`check(<text> != "")`. All 21 examples pass after the rewrite; no assertion
was weakened (`!= nil` / `== nil` / `!= ""` check the identical condition the
original `.?` intended). Spec: same file as above.

## STILL_PRESENT — re-verified 2026-08-17 (P2 triage, compiler lane)

Re-verified at HEAD by source inspection. Note the recorded reproducer
`test/02_integration/lib/.spipe_matchers_persistence_intensive_spec.spl` NO
LONGER EXISTS (only `test/02_integration/lib/persistence_intensive/summary.txt`
remains), so nothing currently covers this idiom.

Root cause unchanged at
`src/compiler/10.frontend/core/interpreter/eval.spl:443-450`: `EXPR_EXISTS_CHECK`
returns the payload, never a bool --
`if val_exists(normalized_vid): return normalized_vid` / `else: return val_make_nil()`.

NOT FIXED by this lane (interpreter path owned by a concurrent P1 lane). A
replacement reproducer is still needed.
