# Seed: `.find()` on a nested `substring()` result fails to resolve — 2026-08-25

Status: FIXED 2026-11-11 (lane p3-comp10) — fix 63c35af09a41 in the tracked seed; spec helper reverted to the single-expression form and is the live pin (16/16 green)

## Symptom

`test/01_unit/app/llm_caret/opencode_cli_spec.spl` (fresh seed from origin/main
`684fadabcae`), `Results: 15 total, 12 passed, 3 failed`:

```
✗ should build then run once and complete while spawn reuses the builder
    semantic: method 'find' not found on value of type str in nested call context
```

Minimal repro (spec on the fresh seed):

```
fn _pos(source: text, needle: text, start: i64) -> i64:
    val relative: i64 = source.substring(start).find(needle)   # <- fails
    relative
expect(_pos("hello world", "world", 2)).to_equal(4)
```

Binding the intermediate first passes:

```
val tail: text = source.substring(start)
val relative: i64 = tail.find(needle)
```

## Workaround applied

`opencode_cli_spec.spl` helper `opencode_source_position_after` now uses the
two-step form (same semantics). After the change the example above passes and
the spec's remaining 2 failures are the separate
`llm_caret_json_parse_nil_contract_and_any_option_wrap_2026-08-25.md` class.

## Unblock condition

Seed: a chained method on a `text`-typed nested call result must resolve like
the same call on a bound `val` (`.claude/rules/language.md` "Chained methods on
erased receivers" — but `substring` returns `text`, so the receiver is not
erased). Once fixed, revert the helper to the single-expression form.

## Triage 2026-11-11 (lane p3-comp10)

Verdict: FIXED. Fresh re-verification at lane base 79d5af6723f6 against the
tracked seed bin/simple.exe (build 46fe8f6b6def, 2026-11-10):

- Root-cause fix: 63c35af09a41 ("fix(seed): dispatch slice/substring on
  temporary text in nested calls", 2026-10-09) IS an ancestor of both the lane
  base and the tracked seed binary. It extends
  src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs so a
  chained method on a `substring()`/`slice` temporary result resolves with the
  same byte-indexed contract as the ordinary string-method path.
- Minimal repro (doc's exact shape): `val relative: i64 =
  source.substring(start).find(needle)` with
  `_pos("hello world", "world", 2) == 4` — fresh run on the tracked seed
  (interpreter) prints `POS=4`, rc=0. Probe at
  build/review/comp10-probes/find_nested_substring.spl. The bound-val two-step
  form passes identically (unchanged behavior).
- Pin restored (the doc's "once fixed, revert the helper" unblock condition):
  test/01_unit/app/llm_caret/opencode_cli_spec.spl helper
  `opencode_source_position_after` is back on the single-expression
  `source.substring(start).find(needle)` form, so every spec run exercises the
  exact nested-call shape. Fresh run on the tracked seed (interpreter,
  --no-cache): outcome=OK executed=16 passed=16 failed=0 rc=0.
