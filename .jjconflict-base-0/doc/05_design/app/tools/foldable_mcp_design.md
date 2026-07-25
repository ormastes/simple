# Foldable MCP Responses with Virtual Diagnostic Lines

**Status:** Design
**Date:** 2026-02-17

## Overview

This document specifies the block-mark format for folded code views in MCP tool responses.
The format enables LLM-efficient code navigation by collapsing function/class bodies and
surfacing diagnostics as virtual lines.

## 1. Three Fold Modes for `simple_read`

| Mode | Bodies | Diagnostics | Use Case |
|------|--------|-------------|----------|
| `full` | Full source | Inline `# [E]` | Current behavior (default) |
| `outline` | `{ ... }` | `V*` per-symbol | LLM token-efficient view |
| `compact` | `{ ... }` | `V*` grouped summary | LLM with error summary |

## 2. Block-Mark Notation

```
F> fn square(x: i64) -> i64 { ... }
V* [E]:5 type mismatch: expected i64, got text
V* [H] cast with .as_i64()
C> class User { name, age, 2 methods }
V* [W]:12 field 'email' is unused
S> struct Point { x, y }
E> enum Color { Red, Green, Blue }
```

### 2.1 Marker Legend

| Marker | Meaning |
|--------|---------|
| `F>` | Collapsed function/method |
| `C>` | Collapsed class |
| `S>` | Collapsed struct |
| `E>` | Collapsed enum |
| `V*` | Virtual diagnostic line |
| `F_` | Expanded function (from expand_at) |
| `C_` | Expanded class (from expand_at) |

### 2.2 Virtual Diagnostic Lines

```
V* [E]:N  <message>   # Error at line N
V* [W]:N  <message>   # Warning at line N
V* [H]    <hint>      # EasyFix hint (no line number)
V* [NE NW in file]    # Compact summary (compact mode)
```

## 3. `expand_at` Tool

Expands a single symbol by name or line number.

### Parameters

| Param | Type | Description |
|-------|------|-------------|
| `path` | string | Path to .spl file |
| `selector` | string | Symbol name or `line:N` |
| `what` | string | `body`, `signature`, or `all` (default) |

### Output

```
F_ fn square(x: i64) -> i64:
    x * x
```

## 4. Data Flow

```
source text
    |
    v
scan_source_symbols()   <-- line-based heuristic
    |
    v
OutlineSym[]
    |
    +---> render_outline(source, entries, mode)
    |           |
    |     block-mark text (returned by simple_read)
    |
    +---> LSP: textDocument/foldingRange
                |
          FoldingRange[] (line ranges for editor folds)
```

## 5. LSP foldingRange Integration

The outline renderer provides the same symbol span data for LSP folding:

- `foldingRangeProvider: true` added to server capabilities
- Handler parses outline and returns `FoldingRange[]` with `startLine`/`endLine`
- Both VSCode and nvim (0.10+) consume this natively via `vim.lsp.foldexpr()`

## 6. Nvim Plugin Brief View

The `:SimpleBrief` command is updated to prefer LSP folding:

1. If LSP client is attached and supports `foldingRange`: use `vim.lsp.foldexpr()`
2. Otherwise: fallback to existing `_fold_expr()` heuristic
