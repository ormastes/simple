# `admit` is a hard keyword and cannot name a function

**Status:** OPEN (low severity, worked around)
**Found:** 2026-08-21, Phase 5 (D4 loader admission) of
`doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`

## Symptom

```
pub fn admit(seal: CompletenessSeal, ...) -> ...
```

fails at parse time with

```
error: compile failed: parse: in ".../admission.spl":
Unexpected token: expected identifier, found Admit
```

The failure is at the `use ... .{admit}` import site as well, so the name is
unusable in both directions.

## Cause

`admit` is a proof-verification statement, alongside `assume` (`Node::Admit`,
`HirStmt::Admit` — `src/compiler_rust/compiler/src/hir/types/statements.rs:90`,
`hir/lower/stmt_lowering.rs:850`). It is lexed as a HARD keyword, not a
contextual one, so it is rejected in every identifier position.

## Why this is worth recording

`assume` and `admit` are proof statements that only ever appear in statement
position followed by a condition expression. They are exactly the shape the
2026-08-17 `move` fix made contextual (`move` is the keyword only when a lambda
introducer or an operand follows it). `admit` and `assume` are not in the
reserved-keyword list in `.claude/rules/language.md`, so the failure is a
surprise at the point of use.

## Workaround in place

`src/compiler/99.loader/completeness_seal/admission.spl` exports
`admit_module` instead of `admit`. The name is not worse, so this is not
blocking — but the compiler should either accept `admit` as a contextual
keyword (preferred, same treatment as `move`) or list it in the language rules
as reserved.

## Unblock condition

Either:
- `admit`/`assume` made contextual in `src/compiler_rust/parser/` (needs a
  rebuilt seed, like the `move` and `examples` fixes), with a regression spec
  next to `test/01_unit/compiler/parser_move_contextual_keyword_spec.spl`; or
- both names added to the **Reserved keywords** list in
  `.claude/rules/language.md`, and this record closed as by-design.
