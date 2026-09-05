# Seed: `.find()` on a nested `substring()` result fails to resolve — 2026-08-25

Status: OPEN (P3) — seed semantic-resolution defect; worked around in ONE spec
helper and recorded here per CLAUDE.md ("fix it or record a concrete bug …
instead of silently normalizing the workaround").

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
