# `.?` truthy-check returns the unwrapped payload (not `true`) when passed directly as a `bool`-typed call argument

## Closed 2026-09-13 — fixed on the lane this entry names (measured); a JIT-lane divergence split out

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

This entry is filed against the evaluator `bin/simple test` uses — the
tree-walk interpreter — so that lane is the one that decides it.

```spl
fn check(condition: bool) -> text:
    if condition == true:
        "EQ-true"
    else:
        "NEQ-true: {condition}"

fn get(f: bool) -> text?:
    if f:
        return "payload"
    nil

fn main():
    print(check(get(true).?))
    print(check(get(false).?))
```

Tree-walk lane (`SIMPLE_EXECUTION_MODE=interpreter run`):

```
EQ-true
NEQ-true: false
```

The `bool`-typed parameter receives a real boolean — `true` for a present
Option, `false` for `nil` — passed **directly** as a call argument with no
intermediate `val`, which is the exact shape this entry says was broken. The
reported symptom (the unwrapped payload — a `Bug` struct, a `text` — arriving
where a `bool` was expected) does not reproduce (measured).

Recorded rather than lost: the **seed JIT** lane is now wrong on the same
program in a different way — `NEQ-true: <special:65>` for the Some case and
`NEQ-true: error` for the nil case, and with a bare `if condition:` it treats
`nil.?` as truthy and takes the wrong branch. That is a distinct defect on a
lane this entry does not cover, so it is filed separately:

`doc/08_tracking/bug/jit_dot_question_as_bool_call_arg_yields_special_value_2026-09-13.md`

The spec-level workaround this entry describes can be removed for the
tree-walk lane, but not for anything that runs through the JIT lane until the
split-out entry is fixed.

- **Date:** 2026-07-20
- **Status:** open (worked around at the spec level, not root-fixed) — CLOSED 2026-09-13 (see top section)
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
