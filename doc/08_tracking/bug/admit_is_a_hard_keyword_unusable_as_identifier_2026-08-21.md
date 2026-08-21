# `admit` is a hard keyword and cannot name a function

**Status:** RESOLVED 2026-08-21 in the seed parser — DEPLOY PENDING (was: OPEN, low severity, worked around)
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

## RESOLVED 2026-08-21 (seed fix implemented + verified; DEPLOY PENDING)

Took the preferred unblock option: `admit`/`assume` are now contextual in the
Rust seed parser, same treatment as `move`. Four sites, all additive:

- `parser/src/parser_helpers.rs` — `expect_identifier()` and
  `expect_path_segment()` accept `Admit`/`Assume` (fixes `use m.lib.{admit}`,
  parameter/field names, aliases).
- `parser/src/expressions/primary/mod.rs` + `primary/identifiers.rs` — primary
  expression position routes them to `parse_primary_identifier` (fixes a bare
  read: `admit + 1`).
- `parser/src/parser_patterns.rs` — usable as a binding pattern
  (`val admit = 5`).
- `parser/src/parser_impl/core.rs` — added to the existing
  `soft_kw_stmt_as_ident` precondition, so `admit = ...` / `admit.field` at
  statement start parse as an assignment rather than a proof statement. A proof
  statement is `admit <cond>`, which can never be followed by `=` or `.`, so the
  keyword meaning is untouched (proved by the last spec scenario).

The lexer already yielded an identifier when `!`/`(` followed, which is why
`fn admit(x)` and `admit(1)` happened to work while every other position failed.

Regression spec: `test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl`
(mirrored byte-identical under `test/unit/compiler/`), next to
`parser_move_contextual_keyword_spec.spl` as the record required.

Evidence, both binaries, same spec, same tree:

- deployed `bin/simple` (pre-fix seed): `executed=0 ... reason=parse-error`,
  `Unexpected token: expected pattern, found Admit` — `Results: 1 total, 0 passed, 1 failed`
- freshly built seed `src/compiler_rust/target/release/simple`:
  `Results: 4 total, 4 passed, 0 failed`
- `cargo test --release -p simple-parser --lib`: `302 passed; 0 failed`
- minimal import repro (`use m.lib.{admit}` + `admit(1)`) prints `2` on the new
  seed; the old seed fails with `expected identifier, found Admit`.

**Remaining:** like the `move` and `examples` fixes, this needs a seed
rebuild + deploy to `bin/release/<triple>/simple` before the spec is green on
the default binary. Not deployed by this lane (a stage1 native-build was in
flight on this host). Until then the spec is RED on `bin/simple` by
construction, exactly as the `move` spec was.
