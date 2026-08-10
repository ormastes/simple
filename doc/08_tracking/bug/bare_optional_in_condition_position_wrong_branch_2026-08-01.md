# Bare `T?` in condition position silently takes the WRONG branch

**Status:** FIXED 2026-08-10 — see "Fix landed" below. Originally found
2026-08-01 while triaging
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

## Fix landed 2026-08-10

Re-examined: this is NOT a genuine two-way language-design fork. Option 2
(reject at compile time) is the one that would silently change the meaning of
code that "compiles today" in a disruptive way (every existing `if opt:` site
turns into a hard error, unmeasured blast radius). Option 1 does not have that
problem, because there is no third behavior being displaced — the ONLY case
whose observable result changes is the absent (`None`) case, which was always
computing the wrong answer (`RT_NIL == 3` read as truthy). The present case
was already correct (any non-nil payload is non-zero and truthy), so it is
unaffected. There is no existing program that could be relying on "absent
optional in condition position takes the then-branch" as correct behavior,
because that state is indistinguishable from a compiler bug from the
program's point of view. So Option 1 is a strict bug fix, not an RFC-worthy
semantics choice.

Implemented in `lower_cond_expr`
(`src/compiler/50.mir/mir_lowering_stmts.spl`, the `case _:` fallthrough
arm): the condition is lowered via `lower_expr` as before, but if the
resulting local's semantic HIR type is `HirTypeKind.Optional(_)`, the raw
value is routed through the same `rt_is_some` runtime call the pre-existing
`ExistsCheck` (`.?`) arm already uses, instead of being branched on directly.
Non-optional conditions are untouched (`cond_local` returned as-is), so `if
b:` for a plain `bool` has zero code-path change.

This does not touch or resolve `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
(a different site: a *bool-typed parameter*, not a raw `if` condition) or the
`.?`-return-type documentation contradiction noted in that file — both remain
open.

**Verification:** repo policy forbids running `bin/simple build bootstrap`
(3-stage self-compile) in this session, and the only locally available
self-hosted binaries (`bootstrap/stage3/simple`, etc.) predate this edit and
cannot be rebuilt from source without that forbidden step, so this fix is
verified by code review only (the added arm is a direct structural mirror of
the pre-existing, already-proven-correct `ExistsCheck` arm nine lines above
it, using the same runtime call, same operand construction, same
sentinel/box-encoding contract) — NOT by an end-to-end execution trace. Anyone
picking this up with bootstrap access should confirm with the repro from
the top of this file:
```
if lookup(false):      # now: else branch (was: THEN branch, wrong)
```

## Related

- `dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20` (OPEN) — a
  neighbouring but distinct defect: an unchecked `bool` PARAMETER coercion lets
  `check(opt.?)` pass `42` into a `bool` slot. Not `.?`-specific; `check(7)`
  does the same.
- `coalesce_on_raw_i64_corrupts_index_3` — same `RT_NIL == 3` sentinel, biting
  in a different operator.
