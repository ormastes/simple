# simple-lsp Claude Plugin

Claude Code plugin bundle for the Simple language server.

## Install

Current Claude Code CLI builds install plugins from marketplaces, not from a
local `--dir` path. Use the checked-in marketplace bundle:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-lsp@simple-local
```

This plugin is intended for use from a Simple repo checkout. It launches:

```bash
bin/simple_lsp_server
```

from the workspace root.

## Common Simple Language Mistakes

See the full [LSP README](../../../src/lib/nogc_sync_mut/lsp/README.md#common-simple-language-mistakes--gotchas) for comprehensive tables. Key traps:

- **Closure mutation lost** — nested functions can read outer vars but modifications don't persist (capture-by-value)
- **`return` in nested `match`** — doesn't propagate, silently falls through. Extract to helper fn
- **Multiline `if` needs parens** — `if (a and\n   b):` works; without parens it fails
- **No inheritance** — `class Child(Parent)` is NOT supported. Use composition/traits/mixins
- **No try/catch** — use `Result<T, E>` + `?` operator
- **Chained methods broken** — `a.f().g()` fails; use intermediate `var`
- **`StructName.new()` deprecated** — use `StructName(field: value)` (DEPR002)
- **`arr = arr + [x]` in loop is O(n^2)** — use `.push(x)` (COLL001)
- **Reserved keywords** — `collect`, `assert`, `gen`, `val`, `def`, `exists`, `actor`, `join`
