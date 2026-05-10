# simple.nvim

Neovim plugin for the [Simple programming language](https://github.com/nicholasgasior/simple).

## Features

- **Filetype detection** for `.spl` files with proper indent and comment settings
- **LSP integration** with auto-detection of the Simple language server (`src/app/lsp/`)
- **Tree-sitter support** with registration and query path management (`src/compiler/parser/treesitter/queries/`)
- **Math block rendering** with conceal for `m{}`, `loss{}`, and `nograd{}` syntax, inline Unicode preview, and LSP hover (LaTeX + Unicode)
- **Test lens** with "▶ Run" virtual text beside `describe`/`it`/`context`/`sdoctest` blocks
- **Test workspace** with structured artifact browsing and rerun/open-source actions
- **Editor markers** for breakpoints, bookmarks, and an execution pointer
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
| `:SimpleTestWorkspace` | Open the structured test workspace |
| `:SimpleBreakpointToggle` | Toggle a breakpoint marker |
| `:SimpleBookmarkToggle` | Toggle a bookmark marker |
| `:SimplePointerToggle` | Toggle the execution pointer marker |
| `:SimplePointerClear` | Clear the execution pointer marker |
| `:SimpleBookmarkNext` | Jump to the next bookmark |
| `:SimpleBookmarkPrev` | Jump to the previous bookmark |
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
| `<localleader>sw` | Test workspace |
| `<localleader>sx` | Toggle breakpoint |
| `<localleader>sk` | Toggle bookmark |
| `<localleader>sp` | Toggle execution pointer |
| `<localleader>s]` | Next bookmark |
| `<localleader>s[` | Previous bookmark |

## Math Block Rendering

Simple supports three math block types: `m{}`, `loss{}`, and `nograd{}`:

```simple
val result = m{ x^2 + y^2 }
val sigmoid = loss{ frac(1, 1 + exp(-x)) }
val init = nograd{ sqrt(frac(6, fan_in + fan_out)) }
```

Math rendering works at two levels:

1. **LSP hover** (primary): The LSP server at `src/app/lsp/handlers/hover.spl` detects
   math blocks and renders them using `src/lib/math_repr.spl`:
   - `render_latex_raw()` -- raw LaTeX output (`$$\frac{1}{1 + \exp(-x)}$$`)
   - `to_pretty()` -- Unicode pretty text (`(1)/(1 + exp(-x))`)
   - `to_md()` -- LaTeX markdown (`$\frac{1}{1 + \exp(-x)}$`)
   - MathJax SVG rendering via `src/lib/mathjax.spl` (requires Node.js)

2. **Inline conceal** (supplementary): With `math.conceal = true`, block delimiters are
   concealed with indicators (∂ math, ℒ loss, ∅ nograd), the interior is highlighted
   with `SimpleMathBlock`, and a Unicode preview is shown as virtual text at end-of-line.
   Hovering over a math block shows the original source in a floating window.

**Inline Unicode rendering** converts structured expressions:

| Expression | Renders As |
|------------|------------|
| `frac(1, 2)` | `(1)/(2)` |
| `sqrt(x)` | `√(x)` |
| `x^2` | `x²` |
| `alpha + beta` | `α + β` |
| `sum(i, 0..n) i` | `∑(i=0..n) i` |
| `int(x, 0..1) x` | `∫(x=0..1) x` |
| `A'` | `Aᵀ` |
| `a .* b` | `a ⊙ b` |
| `\frac{a}{b}` | `(a)/(b)` |

## Test Lens

When editing `.spl` files, virtual text "▶ Run" indicators appear beside test blocks:

- `describe "...":`  → **▶ Run File**
- `it "...":`        → **▶ Run Test**
- `context "...":`   → **▶ Run Test**
- `""" sdoctest:`    → **▶ Run Doctest**

Use `:SimpleMathToggle` to toggle math rendering, or call `require("simple.test_lens").toggle()` for test lens.

## Test Workspace

`SimpleTestWorkspace` opens a scratch buffer that lists the latest structured
test-runner artifacts from `build/test-artifacts/`.

Inside the workspace:

- the header shows total / passed / failed / skipped counts
- `r` refreshes the artifact list
- `<CR>` opens the source file for the selected result
- `R` reruns the selected test file
- `o` opens the selected artifact directory in the OS file manager
- `l` opens the latest result's source file

This is a companion view, not a replacement editor. Source edits remain in the
real `.spl` buffer.

## Editor Markers

`simple.nvim` can show editor-local markers for:

- breakpoint toggles
- bookmarks / anchors
- a current execution pointer

These markers are exposed through gutter signs and can be navigated with
`SimpleBookmarkNext` / `SimpleBookmarkPrev`.

## Diagnostics

Simple files use stronger diagnostics presentation by default:

- rounded floating windows for error details
- visible gutter signs for errors, warnings, info, and hints
- severity-sorted diagnostics
- virtual-text markers with a visible bullet prefix

Use `<leader>e` to open the diagnostic float and `<leader>q` to send issues to
the location list.

## Neovim Key Hints

The default `<localleader>s` mappings include:

- `<localleader>sw` for the test workspace
- `<localleader>sx` for breakpoints
- `<localleader>sk` for bookmarks
- `<localleader>sp` for the execution pointer
- `<localleader>s[` and `<localleader>s]` for bookmark navigation

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
