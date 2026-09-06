---
paths:
  - "**/*.spl"
  - "**/*.shs"
alwaysApply: false
---
# Simple Language Rules

- **ALL code in `.spl` or `.shs`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Scripts:** Use `.shs` for shell scripts that need to remain shell (e.g., container entrypoints)
- **Pure Simple first; C is a boundary; asm last.** Never write C when pure Simple can do it; bootstrap-required C keeps a pure-Simple twin (dual-run gate `scripts/check/check-dual-run-shadow.shs`); HAL code prefers typed register views > no-reorder/no-elide tags > intrinsics > inline asm (irreplaceable ops only). Full policy: `doc/07_guide/os/hal/pure_simple_hal.md`
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **NO inheritance** - `class Child(Parent)` is NOT supported. Use composition, alias forwarding, traits, or mixins instead
- **SDN format** for all config/data files, not JSON/YAML
- **Error handling:** Use `Result<T, E>` + `?` operator (no try/catch/throw keywords — by design)

## Runtime Limitations
- **Multi-line booleans** continue naturally after a trailing `and`/`or` — no parentheses needed. Do NOT add `(...)` merely for line continuation (user directive 2026-09-05: it hurts readability); parens are for precedence grouping only. See `doc/08_tracking/bug/stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`.
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY (module closures work fine)
- **Chained methods on erased receivers** - chains fail only when a link's receiver type is erased (e.g. from ANY/dict); typed chains work. Workaround: intermediate typed `val`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`, `examples`, `and_then`
- **`examples` and `and_then`** — FIXED (2026-08-17): both are now accepted as named-argument labels (`Foo(examples: x)`, `Foo(and_then: y)`), alongside every other soft keyword. Census run 2026-08-10 had found these two to be the ONLY broken identifiers in that lexer block — `scenario`, `given`, `when`, `then`, `feature`, `outline` were always fine. The fix lands in `src/compiler_rust/parser/src/expressions/helpers.rs`; **it requires a rebuilt seed** — a binary older than 2026-08-17 still reports `function arguments: expected Comma, found Colon`. Regression spec: `test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl`. See `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`
- **`move`** — FIXED (2026-08-17): `move` is now contextual. `var move = 3u32` followed by `while move + 1u32 < n` used to fail with `parse: Unexpected token: expected expression, found Plus`; `move` is treated as the keyword only when a lambda introducer or an operand follows it, and is an ordinary identifier otherwise. Move-closures (`move \x: ...`) are unaffected. **Requires a rebuilt seed** — an older binary still reports the Plus error. Regression spec: `test/01_unit/compiler/parser_move_contextual_keyword_spec.spl`. See `doc/08_tracking/bug/move_identifier_rejected_as_expression_2026-08-15.md`
- **`generator`** — an ordinary name, but the interpreter has a lambda-based `generator(fn)` builtin. A user-defined `fn generator(...)` (e.g. `src/lib/nogc_async_mut/generator.spl`) shadows it as of 2026-08-17; on an older binary any call through that module fails with `semantic: generator expects a lambda`. See `doc/08_tracking/bug/generator_identifier_collides_with_builtin_construct_name_2026-08-11.md`
- **`auto`** — FIXED (2026-09-05): `auto` is a hard keyword (auto modules) and was rejected as a named-argument label (`P(auto: true)` → `expected Comma, found Colon`), while field declaration, `.auto` reads, and positional construction worked. Now accepted as a label like `examples`/`and_then`. **Requires a rebuilt seed.** Regression spec: `test/01_unit/compiler/parser_auto_contextual_keyword_spec.spl`. See `doc/08_tracking/bug/auto_keyword_rejected_as_named_argument_label_2026-09-05.md`
- **`admit` / `assume`** — FIXED (2026-08-21): both are now contextual. They are the keyword only in statement position followed by a condition; every identifier position (`use m.lib.{admit}`, `val admit = 5`, `admit + 1`, `admit = x`, parameter/field names) is an ordinary name. `fn admit(...)` and `admit(1)` always worked because the lexer already special-cased a following `(`. **Requires a rebuilt seed** — an older binary still reports `Unexpected token: expected identifier, found Admit`. Regression spec: `test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl`. See `doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md`

## Syntax Quick Reference
See `doc/07_guide/quick_reference/syntax_quick_reference.md` for complete reference.
See `.claude/memory/ref_coding.md` for coding conventions and common mistakes.
