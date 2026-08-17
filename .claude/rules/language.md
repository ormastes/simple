---
paths:
  - "**/*.spl"
  - "**/*.shs"
alwaysApply: false
---
# Simple Language Rules

- **ALL code in `.spl` or `.shs`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Scripts:** Use `.shs` for shell scripts that need to remain shell (e.g., container entrypoints)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **NO inheritance** - `class Child(Parent)` is NOT supported. Use composition, alias forwarding, traits, or mixins instead
- **SDN format** for all config/data files, not JSON/YAML
- **Error handling:** Use `Result<T, E>` + `?` operator (no try/catch/throw keywords — by design)

## Runtime Limitations
- **Multi-line booleans** - wrap in parentheses: `if (a and\n   b):` works
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY (module closures work fine)
- **Chained methods on erased receivers** - chains fail only when a link's receiver type is erased (e.g. from ANY/dict); typed chains work. Workaround: intermediate typed `val`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`, `examples`, `and_then`
- **`examples` and `and_then`** — FIXED (2026-08-17): both are now accepted as named-argument labels (`Foo(examples: x)`, `Foo(and_then: y)`), alongside every other soft keyword. Census run 2026-08-10 had found these two to be the ONLY broken identifiers in that lexer block — `scenario`, `given`, `when`, `then`, `feature`, `outline` were always fine. The fix lands in `src/compiler_rust/parser/src/expressions/helpers.rs`; **it requires a rebuilt seed** — a binary older than 2026-08-17 still reports `function arguments: expected Comma, found Colon`. Regression spec: `test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl`. See `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`
- **`generator`** — an ordinary name, but the interpreter has a lambda-based `generator(fn)` builtin. A user-defined `fn generator(...)` (e.g. `src/lib/nogc_async_mut/generator.spl`) shadows it as of 2026-08-17; on an older binary any call through that module fails with `semantic: generator expects a lambda`. See `doc/08_tracking/bug/generator_identifier_collides_with_builtin_construct_name_2026-08-11.md`

## Syntax Quick Reference
See `doc/07_guide/quick_reference/syntax_quick_reference.md` for complete reference.
See `.claude/memory/ref_coding.md` for coding conventions and common mistakes.
