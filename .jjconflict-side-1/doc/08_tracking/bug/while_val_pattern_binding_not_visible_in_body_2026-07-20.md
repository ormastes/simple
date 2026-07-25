# Bug: `while val Pattern(x) = expr:` loop body cannot see `x` (`variable not found`)

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/pattern_matching_advanced_spec.spl`)
- **Area:** `while val`/`while let` pattern-binding scope (interpreter or HIR
  lowering, not isolated further in this pass), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

```
✗ loops while pattern matches
  semantic: variable `value` not found
```

The spec originally used `while let Some(value) = next_item(counter):` — per
`.claude/rules/language.md` ("Pattern binding: `if val` not `if let`"), `let`
is not Simple's keyword here, so this pass first corrected the spec to `while
val Some(value) = next_item(counter):`. The error is **identical** either way
— this rules out "wrong keyword" as the (sole) cause and confirms a genuine
binding-scope gap for `while val`/`while let` pattern destructuring
specifically (as opposed to `if val`, which per the same language rule is the
documented/working form and is used successfully elsewhere in this test
cluster, e.g. throughout `safe_unwrap_operators_spec.spl` fixes in this same
pass).

## Minimal repro

```simple
describe "repro":
    it "while val binds pattern var":
        fn next_item(n: i64) -> Option<i64>:
            if n > 0:
                Some(n)
            else:
                None

        var counter = 3
        var sum = 0
        while val Some(value) = next_item(counter):
            sum = sum + value
            counter = counter - 1
        expect sum == 6
```

`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`:
```
✗ while val binds pattern var
  semantic: variable `value` not found
```

## Root cause

Not isolated to a specific source location in this pass. The loop condition's
pattern-bound variable (`value`, from `Some(value)`) is evidently not being
registered into the loop body's scope, unlike `if val Pattern(x) = expr:` whose
bound variable IS visible inside the `if` body (used successfully throughout
this repo's specs).

## Fix direction (not applied — compiler-internals change, needs rebuild)

Compare the scope-binding logic for `if val`/`if let` (working) against
`while val`/`while let` (broken) in the parser/HIR-lowering/interpreter and
apply the same binding mechanism to the loop-body scope.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/pattern_matching_advanced_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.
