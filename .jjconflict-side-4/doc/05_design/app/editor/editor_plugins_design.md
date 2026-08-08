# Editor Extension Design: Unicode Beautification

## Overview

Editor extensions for Simple that provide Unicode-rendered display of
operators, math blocks, Markdown blocks, and custom blocks. The shared in-repo
extension model lives under `src/lib/editor/extensions/` and uses
`extension.sdn` manifests. Host ecosystem adapters can still use their native
packaging names, for example `simple.nvim` for Neovim and a VS Code-compatible
extension adapter, but reusable behavior belongs in the shared editor library.

## Conceal Rules (Editor Extensions)

Applied in normal/view mode only; raw text shown in insert mode.

| Source | Concealed | Context |
|--------|-----------|---------|
| `\|>` | `▸` | Pipeline forward |
| `>>` | `⊳` | Compose forward |
| `<<` | `⊲` | Compose backward |
| `~>` | `⇝` | Layer connect |
| `//` | `∥` | Parallel |
| `->` | `→` | Return type arrow |
| `=>` | `⇒` | Fat arrow |
| `!=` | `≠` | Not equal |
| `<=` | `≤` | Less or equal |
| `>=` | `≥` | Greater or equal |
| `not` | `¬` | Logical not |
| `and` | `∧` | Logical and |
| `or` | `∨` | Logical or |
| `xor` | `⊕` | Bitwise XOR |
| `fn` | `λ` | Function keyword (optional, off by default) |
| `forall` | `∀` | Universal quantifier |
| `exists` | `∃` | Existential quantifier |

## Neovim Host Adapter (`simple.nvim`)

### Architecture

- Tree-sitter conceal queries via `nvim-treesitter`
- Virtual text via `nvim.api.nvim_buf_set_extmark()` for block rendering
- Math block preview: virtual text below `m{...}` showing Unicode form
- Toggle with `<leader>m`

### Dependencies

- `tree-sitter-simple` grammar (separate repo)
- `nvim-treesitter` for conceal integration

### Conceal Query Example

```scheme
;; highlights.scm for tree-sitter-simple
(pipeline_operator "|>" @conceal (#set! conceal "▸"))
(arrow_operator "->" @conceal (#set! conceal "→"))
(not_keyword "not" @conceal (#set! conceal "¬"))
```

### Configuration

```lua
require("simple").setup({
  conceal = {
    enable = true,
    fn_lambda = false,  -- fn -> λ (off by default)
  },
  math_preview = {
    enable = true,
    keymap = "<leader>m",
  },
})
```

## VS Code-Compatible Host Adapter

### Architecture

- `TextEditorDecorationType` for inline operator beautification
- `CompletionItemProvider` for Lean-style Unicode input (`\alpha` + Tab -> `α`)
- `HoverProvider` for math/lean block preview
- LSP integration via shared editor render/extension services for hover/inlay hints
- Markdown-first preview support for notes, wiki links, callouts, tables, tasks,
  and attachments

### Unicode Input Method

| Input | Output | Description |
|-------|--------|-------------|
| `\alpha` | `α` | Greek alpha |
| `\beta` | `β` | Greek beta |
| `\gamma` | `γ` | Greek gamma |
| `\pi` | `π` | Pi |
| `\sum` | `∑` | Summation |
| `\sqrt` | `√` | Square root |
| `\forall` | `∀` | Universal quantifier |
| `\exists` | `∃` | Existential quantifier |
| `\to` | `→` | Arrow |
| `\lambda` | `λ` | Lambda |
| `\inf` | `∞` | Infinity |

### LSP Integration

The runtime's Rich render mode (`blocks::render_mode::RenderMode::Rich`) returns structured JSON:

```json
{
  "type": "math",
  "source": "x^2 + alpha",
  "unicode": "x² + α"
}
```

The LSP server can use this for:
- Hover previews over `m{...}` blocks
- Inlay hints showing rendered form after block close
- Code lens with rendered math above/below

## Implementation Order

1. Shared editor extension manifest and command contribution contracts
   (`src/lib/editor/extensions/`, `extension.sdn`)
2. Markdown-first preview/beautification commands in the shared editor library
3. Tree-sitter grammar (`tree-sitter-simple`) for host adapters that need it
4. `simple.nvim` with conceal queries + math/Markdown virtual text
5. VS Code-compatible adapter with decorations + Unicode input + hover
6. LSP integration through shared render services
