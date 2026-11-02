# Seed: a value-position `match` with no matching arm silently yields nil/0

Status: OPEN. Severity: P2. Found 2026-11-02 by lane pattern-lowering-audit.
Checked against current policy/design: nil is allowed only inside `unsafe`,
Any only inside `unsafe`, and generics are erased. Runtime exhaustiveness
behaviour is set by `SIMPLE_SAFETY_PROFILE` (doc/07_guide/language/strictness_tiers.md).

## Same class as the case-nil fix
The `case nil:` lowering to `rt_string_eq(subject, nil)` (fix owned by the
s2-rebuild lane) did real damage only because a failed match falls through
silently. The arm never matched, the match yielded nil, and the caller used
that nil (the stage2_next worker AV). If fall-through failed closed, that bug
would have stopped loudly at the match.

## Evidence (seed, run with worktree bin/simple.exe = Rust seed)
```
fn pick(s: text) -> i64:
    match s:
        case "a": 1
        case "b": 2
pick("z")        # prints 0, rc=0, no diagnostic
ipick(5)         # int subject, arms -1 / i64::MAX, prints 0
```
Literal kinds checked and correct on the seed: text, negative int, i64 max,
None/Some on `text?`.

Source: src/compiler_rust/compiler/src/hir/lower/expr/control.rs
`lower_match_arms`: when `arms.is_empty()` it returns `HirExprKind::Nil`.

## Pure-Simple compiler status
- Partial enum matches with no default already lower to rt_panic+Abort
  (match_enum_fallthrough_silent_2026-08-01, fixed 2026-09-19).
- Scalar/text/tuple if-chain value matches still yield a `Const(Int(0))`
  placeholder (switch_operators_calls.spl cascade tail) and are tracked by
  if_chain_match_no_arm_matched_is_silent_2026-10-10 (OPEN).

## Other seed literal-equality suspects (code reading, not confirmed)
- control.rs `lower_pattern_condition` Pattern::Literal: picks `rt_string_eq`
  when EITHER side is text/char. So a text-typed subject with a non-text
  literal (nil was the observed case) gets text equality. The general fix is
  to choose equality from the literal kind first (nil -> rt_is_none) and use
  text equality only when the literal is a text/char literal.
- control.rs `subpattern_condition` Pattern::Literal (payload slot, ANY):
  a nested `nil` literal lowers to `BinOp::Eq(slot, nil)`, not `rt_is_none`,
  so a boxed-None payload may not match. Under current policy `case nil` is
  non-compliant outside unsafe anyway; the target is `case None`.

## Proposed rule (not in the current spec)
A value-position `match` that finds no arm MUST fail closed:
rt_panic("non-exhaustive match: no arm matched") followed by an abort, on
every lane, whatever SIMPLE_SAFETY_PROFILE is set to. A statement match keeps
no-op semantics unless the critical profile is set. The strictness-tiers
guide currently specifies only interpreter diagnostics (warn by default,
error under critical), so this needs a spec change before it becomes compiler
behaviour. Do not change the seed first: bootstrap sources may depend on the
fall-through.

## Blast radius (git grep, src/**/*.spl excluding compiler_rust, 2026-11-02)
case nil: 1605 | case None: 691 | case true/false: 2/2 | negative int
literal arms: 13 | float literal arms: 2 | char-literal arms: 16 |
text or-pattern arms: 339 | `== nil`: 5339 | `!= nil`: 2601 |
`== None`: 15 | `!= None`: 4
