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
- **Chained methods broken** - use intermediate `var`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`

## Syntax Quick Reference
See `doc/07_guide/quick_reference/syntax_quick_reference.md` for complete reference.
See `.claude/memory/ref_coding.md` for coding conventions and common mistakes.
