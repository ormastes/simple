# simple-lsp

Simple language server plugin for Claude Code.

Runtime:

```bash
bin/release/simple run src/app/lsp/main.spl
```

## Common Simple Language Mistakes

### Critical Runtime Issues

| Mistake | What Happens | Fix |
|---------|-------------|-----|
| Mutating outer var in closure | Changes silently lost (capture-by-value) | Return modified value instead |
| `return` inside nested `match` | Return doesn't propagate, falls through | Extract inner match to helper function |
| `.push()` on module-level var from function | Array change not visible at module level | Use return values or local vars |
| Multiline `if` without parens | Parse failure or wrong behavior | Wrap: `if (a and`<br>`   b):` |

### Syntax Pitfalls

| Mistake | Diagnostic | Fix |
|---------|-----------|-----|
| `class Child(Parent)` | Error | No inheritance. Use composition, traits, or mixins |
| `StructName.new(args)` | DEPR002 | Use `StructName(field: value)` |
| `Type__method()` | DEPR001 | Use `Type.method()` |
| Bare `pass` | DEPR003 | Use `pass_do_nothing` or `pass_todo` |
| `s[:idx]` or `s[:-1]` | Parse error | Use `s[0:idx]` or `s[0:s.len()-1]` |
| Chained methods `a.f().g()` | Runtime error | Use intermediate `var`: `var t = a.f(); t.g()` |

### Performance Anti-patterns

| Mistake | Code | Fix |
|---------|------|-----|
| `arr = arr + [x]` in loop | COLL001 | Use `.push(x)` |
| `str = str + x` in loop | COLL006 | Collect to array, `.join()` |
| `.contains()` in loop | COLL002 | Use `Dict` for O(1) lookup |

### LSP Diagnostic Codes

| Code | Meaning | Rendering |
|------|---------|-----------|
| UNUSED001-003 | Unused var/import/param | Faded |
| UNREACH001-003 | Unreachable code | Faded |
| DEPR001-003 | Deprecated syntax | Strikethrough |
| COLL001-008 | Collection anti-patterns | Warning |
| CLOS001 | Closure modifies outer var | Warning |
| RET001 | Discarded return value | Info |
| BOOL001 | Multiline bool without parens | Warning |
| MEXH001-002 | Non-exhaustive match | Warning |
| ARG001-002 | Too many parameters | Warning/Error |
| SAFE001/003 | Unsafe outside `unsafe` | Error |

### Reserved Keywords

Cannot be used as names: `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`, `collect`, `shared`

### Quick Reference

- **Generics:** `Option<T>`, `List<Int>` (use `<>` not `[]`)
- **Optional check:** `value.?` (not `value?`)
- **Null coalescing:** `value ?? default`
- **Error handling:** `Result<T, E>` + `?` (no try/catch)
- **Immutable:** `val x = 1` or `x := 1`
- **Mutable self:** `me method()` not `fn method()`
