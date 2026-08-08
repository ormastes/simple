# Bare `T?` in condition position silently takes the WRONG branch

**Status:** OPEN — found 2026-08-01 while triaging
`optional_query_operator_identity_passthrough_2026-07-20` (which was itself
INVALID; this is the real defect in the neighbourhood).

**Severity:** high — silent wrong result, no diagnostic.

## Symptom

Using an optional directly as a condition, without `.?`, takes the branch for
"present" even when the value is absent:

```
if lookup(false).?:    # -> else branch   (CORRECT)
if lookup(false):      # -> THEN branch   (WRONG)
```

## Why

`RT_NIL` is the sentinel value `3`, which is non-zero and therefore truthy
under a plain truthiness test. So an absent optional reads as present.

This is the exact hazard the `lower_cond_expr` docstring
(`src/compiler/50.mir/mir_lowering_stmts.spl:1468-1494`) warns about. That
function implements a deliberate position split — `.?` in VALUE position keeps
the payload, `.?` in CONDITION position lowers to `rt_is_some` — but the split
only fires when `.?` is present. A bare optional never reaches it.

## Why this is not the same bug as the one that found it

`optional_query_operator_identity_passthrough_2026-07-20` claimed `.?` should
return `bool` and was closed INVALID: `.?` is specified to return `T?` in three
independent places (`doc/07_guide/quick_reference/syntax_quick_reference.md:505`,
`src/compiler/10.frontend/parser_types_expr.spl:229`, and the MIR position split
above). This defect is the INVERSE — not `.?` doing the wrong thing, but a
MISSING `.?` being silently accepted where it changes the answer.

## Open question for whoever owns this

Two defensible fixes, and the choice is a language decision rather than a bug
fix, so it is recorded rather than guessed:

1. Make a bare `T?` in condition position lower through `rt_is_some` too, so
   `if x:` and `if x.?:` agree.
2. Reject a bare `T?` in condition position as a type error, forcing `.?`.

Option 2 matches the existing idiom guidance (`.claude/rules/language.md:14`
prefers `.?` over `is_*` predicates) and turns a silent wrong answer into a
compile error, which is the better failure mode. Option 1 is friendlier but
leaves two spellings meaning the same thing.

Not fixed here: picking one silently changes the meaning of existing code that
compiles today.

## Related

- `dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20` (OPEN) — a
  neighbouring but distinct defect: an unchecked `bool` PARAMETER coercion lets
  `check(opt.?)` pass `42` into a `bool` slot. Not `.?`-specific; `check(7)`
  does the same.
- `coalesce_on_raw_i64_corrupts_index_3` — same `RT_NIL == 3` sentinel, biting
  in a different operator.
