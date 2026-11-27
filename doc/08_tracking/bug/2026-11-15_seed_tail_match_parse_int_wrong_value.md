# Seed interpreter: tail-position `match raw.parse_i64()` returned a wrong value (observed, NOT minimised)

Date: 2026-11-15
Status: observed in a larger function, not reproduced in any minimal form
Component: Rust seed interpreter (`bin/simple.exe`), match / call-result handling

## Symptom (as observed in the release/1.0.0 bootstrap campaign)

A function whose last expression was `match raw.parse_i64():` with
`case Some(n): <expr using n>` returned a wrong, shared-looking value on the
Rust seed. Binding the result first (`val parsed = raw.parse_i64()` then
`match parsed:`, or `val out = match ...` then `out`) gave the right value.
The exact original function was not preserved, so the wrong/expected values
of the original are unknown.

## Reproduction attempt

Spec: `test/01_unit/compiler/interpreter/tail_match_parse_int_repeat_call_spec.spl`
(8 cases, committed as a regression guard). Forms tried, each called 3-4 times
with different inputs, including a repeat of the first input (a "second call
returns the first call's value" defect would fail these):

- tail `match raw.parse_int():` and tail `match raw.parse_i64():` (Some/None)
- bound Option then match; `val out = match ...` then `out`
- method on a struct with a `case _` wildcard arm, driven from a `for` loop
- `raw.trim().parse_int()` returning a wrapper struct
- tail `match` on a user `Result<i64, text>` (Ok/Err)

Result: all PASS. No wrong value was produced.

```
Results: 8 total, 8 passed, 0 failed
```

Not tried: the original callee's surrounding context (module-level state,
closures, generic callers, very deep call chains), and the pure-Simple binary
(none deployed on this host).

Note: `src/lib/common/text.spl:5` defines a FREE `fn parse_i64(s) -> i64`
(returns `-1` on failure) that is a different thing from the `.parse_i64()`
method returning `Option`; a tail `match` over the free function's `i64` would
not compile into Some/None arms, which is one possible source of a mismatch in
the original code.

## Binary identity

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```
`bin/simple.exe`: 37622272 bytes, mtime 2026-11-15 12:24:16 +0900; release tip 2cf3dc7e5ec.

## Workaround in use

Bind the parse result to a `val` before matching.

## Unblock condition

Capture the failing original function (git history of the campaign lane) and
diff it against the forms above; extend the spec with the first form that goes
RED, tag it `# @tag:in-development` in its own file pointing at this record,
then fix in the seed.
