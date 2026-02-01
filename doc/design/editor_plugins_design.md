# Editor Plugin Design: Unicode Beautification

## Overview

Editor plugins for Simple that provide Unicode-rendered display of operators, math blocks, and custom blocks. Two plugins: `simple.nvim` (Neovim) and `simple-vscode` (VS Code).

## Conceal Rules (Both Editors)

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

## Neovim Plugin (`simple.nvim`)

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

## VS Code Extension (`simple-vscode`)

### Architecture

- `TextEditorDecorationType` for inline operator beautification
- `CompletionItemProvider` for Lean-style Unicode input (`\alpha` + Tab -> `α`)
- `HoverProvider` for math/lean block preview
- LSP integration via Rich render mode for hover/inlay hints

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

1. Tree-sitter grammar (`tree-sitter-simple`) -- prerequisite for nvim plugin
2. `simple.nvim` with conceal queries + math virtual text
3. `simple-vscode` with decorations + Unicode input + hover
4. LSP integration (requires Rich render mode, already implemented in runtime)
