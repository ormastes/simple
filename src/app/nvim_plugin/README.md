# simple.nvim

Neovim plugin for the [Simple programming language](https://github.com/nicholasgasior/simple).

## Features

- **Filetype detection** for `.spl` files with proper indent and comment settings
- **LSP integration** with auto-detection of the Simple language server (`src/app/lsp/`)
- **Tree-sitter support** with registration and query path management (`src/compiler/parser/treesitter/queries/`)
- **Math block rendering** with conceal for `m{ ... }` syntax, inline Unicode preview, and LSP hover (LaTeX + Unicode)
- **Brief view** for code overview (fold to signatures only)
- **User commands** for testing, building, linting, and formatting
- **Health checks** via `:checkhealth simple`

## Requirements

- Neovim >= 0.9 (0.11+ recommended for native LSP config)
- Simple language compiler (`bin/simple`) for LSP and test/build commands
- Optional: [nvim-treesitter](https://github.com/nvim-treesitter/nvim-treesitter) for tree-sitter parser management

## Installation

### lazy.nvim

```lua
{
  "nicholasgasior/simple.nvim",
  ft = "simple",
  opts = {},
}
```

### packer.nvim

```lua
use {
  "nicholasgasior/simple.nvim",
  config = function()
    require("simple").setup()
  end,
}
```

### Manual (from project)

Add the plugin directory to your runtime path in `init.lua`:

```lua
vim.opt.rtp:prepend("/path/to/simple/src/app/nvim_plugin")
require("simple").setup()
```

## Configuration

```lua
require("simple").setup({
  lsp = {
    enabled = true,
    cmd = { "simple", "lsp" },        -- or { "bin/simple", "lsp" }
    root_markers = { "simple.sdn", ".git" },
    settings = {},
    on_attach = nil,                    -- custom on_attach callback
  },
  math = {
    enabled = true,
    conceal = true,                     -- conceal m{ } delimiters
    float_on_hover = true,              -- show float on CursorHold
    update_delay = 100,                 -- ms debounce for re-rendering
    highlight_group = "SimpleMathBlock",
  },
  treesitter = {
    ensure_installed = true,
    query_path = nil,                   -- auto-detects from project
  },
  commands = {
    enabled = true,
    test_cmd = { "bin/simple", "test" },
  },
  keymaps = {
    enabled = true,
    prefix = "<localleader>s",
  },
})
```

## Commands

| Command | Description |
|---------|-------------|
| `:SimpleTest [file]` | Run tests on current file or specified path |
| `:SimpleBrief` | Collapse all folds to show only signatures |
| `:SimpleBriefExpand` | Expand all folds |
| `:SimpleLspRestart` | Restart the Simple LSP server |
| `:SimpleLspLog` | Open the LSP log file |
| `:SimpleMathToggle` | Toggle math block rendering |
| `:SimpleBuild [args]` | Run build command with optional arguments |
| `:SimpleLint` | Run the Simple linter |
| `:SimpleFormat` | Run the Simple formatter |
| `:SimpleInfo` | Show plugin information |

## Default Keymaps

When `keymaps.enabled = true`, the following keymaps are set for Simple files
(prefix defaults to `<localleader>s`):

| Keymap | Action |
|--------|--------|
| `<localleader>st` | Run test |
| `<localleader>sb` | Brief view |
| `<localleader>se` | Expand all |
| `<localleader>sm` | Toggle math |
| `<localleader>sr` | Restart LSP |
| `<localleader>si` | Plugin info |
| `<localleader>sl` | Lint |
| `<localleader>sf` | Format |

## Math Block Rendering

Simple supports math blocks with the `m{ ... }` syntax:

```simple
val result = m{ x^2 + y^2 }
val gradient = m{ d/dx (x^2) }
```

Math rendering works at two levels:

1. **LSP hover** (primary): The LSP server at `src/app/lsp/handlers/hover.spl` detects
   `m{ }` blocks and renders them using `src/lib/math_repr.spl`:
   - `render_latex_raw()` -- raw LaTeX output (`$$x^{2} + y^{2}$$`)
   - `to_pretty()` -- Unicode pretty text (`x² + y²`)
   - `to_md()` -- LaTeX markdown (`$x^{2} + y^{2}$`)
   - MathJax SVG rendering via `src/lib/mathjax.spl` (requires Node.js)

2. **Inline conceal** (supplementary): With `math.conceal = true`, the `m{` and `}`
   delimiters are concealed, the interior is highlighted with `SimpleMathBlock`, and
   a Unicode preview is shown as virtual text at end-of-line (e.g., `x² + y²`).
   Hovering over a math block shows the original source in a floating window.

## Tree-sitter Queries

The plugin automatically locates tree-sitter queries from the Simple project at
`src/compiler/parser/treesitter/queries/`. These include:

- `highlights.scm` (538 lines) - Syntax highlighting (100+ keywords, 50+ scope types, operators, literals)
- `locals.scm` (411 lines) - Scope tracking and variable resolution
- `folds.scm` (404 lines) - Code folding regions
- `textobjects.scm` (587 lines) - Semantic text objects for selection/navigation
- `injections.scm` (373 lines) - Embedded language support (15+ injected languages including SQL, HTML, regex)
- `indents.scm` (454 lines) - Auto-indentation rules

## Health Check

Run `:checkhealth simple` to verify:

- Neovim version compatibility
- LSP server binary availability
- Tree-sitter parser installation
- Math rendering status
- Project structure detection

## License

Same license as the Simple language project.
