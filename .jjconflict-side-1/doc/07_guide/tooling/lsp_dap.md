# LSP and DAP Integration Guide

Setup and usage for the Simple Language Server Protocol (LSP) and Debug Adapter Protocol (DAP) in VS Code and Neovim.

---

## LSP Overview

The Simple LSP server provides code intelligence over JSON-RPC 2.0 via stdio.

```bash
# Start the LSP server
bin/simple lsp

# Run LSP tests
bin/simple test test/unit/app/lsp/
```

### Features

| Feature | Description | Keybind (Neovim) | Keybind (VS Code) |
|---------|-------------|------------------|-------------------|
| Go to Definition | Jump to symbol definition | `gd` | F12 |
| Find References | Find all usages | `gr` | Shift+F12 |
| Hover Info | Type info and docs | `K` | Mouse hover |
| Completion | Intelligent autocomplete | `<C-Space>` | Ctrl+Space |
| Diagnostics | Real-time error checking | `]d` / `[d` | Problems panel |
| Document Sync | Incremental sync | automatic | automatic |

Planned: code actions (refactoring), semantic highlighting, call hierarchy, type hierarchy.

### Server Configuration

Configure via `.simple/lsp-config.sdn`:

```sdn
{
  diagnostics: {
    enabled: true
    on_type: true
    on_save: true
    debounce_ms: 200
  }
  completion: {
    enabled: true
    trigger_characters: [".", ":", ">"]
    max_items: 100
  }
  hover: {
    enabled: true
    show_type: true
    show_docs: true
  }
  logging: {
    level: "info"
    file: ".simple/lsp.log"
  }
}
```

---

## VS Code Setup

### LSP Configuration

Create `.vscode/settings.json`:

```json
{
  "simple.lsp.enabled": true,
  "simple.lsp.serverPath": "simple",
  "simple.lsp.serverArgs": ["lsp", "start"],
  "simple.lsp.trace.server": "messages",
  "simple.lsp.diagnostics.enable": true,
  "simple.lsp.diagnostics.delay": 500,

  "[simple]": {
    "editor.formatOnSave": true,
    "editor.tabSize": 4,
    "editor.insertSpaces": true
  },

  "files.associations": {
    "*.spl": "simple",
    "*.spipe": "simple"
  }
}
```

### Language Configuration

Create `.vscode/language-configuration.json`:

```json
{
  "comments": {
    "lineComment": "#",
    "blockComment": ["#[", "]#"]
  },
  "brackets": [
    ["{", "}"],
    ["[", "]"],
    ["(", ")"]
  ],
  "autoClosingPairs": [
    { "open": "{", "close": "}" },
    { "open": "[", "close": "]" },
    { "open": "(", "close": ")" },
    { "open": "\"", "close": "\"", "notIn": ["string"] }
  ]
}
```

### DAP Configuration

Add to `.vscode/launch.json`:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Debug Simple Program",
      "type": "simple",
      "request": "launch",
      "program": "${file}",
      "cwd": "${workspaceFolder}",
      "stopOnEntry": true,
      "console": "integratedTerminal",
      "debugAdapter": {
        "type": "executable",
        "command": "simple",
        "args": ["dap", "start", "--stdio"]
      }
    },
    {
      "name": "Debug Simple Tests",
      "type": "simple",
      "request": "launch",
      "program": "${workspaceFolder}/test",
      "args": ["--test-runner"],
      "cwd": "${workspaceFolder}",
      "stopOnEntry": false
    }
  ]
}
```

### Build Tasks

Create `.vscode/tasks.json`:

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "build-simple",
      "type": "shell",
      "command": "simple",
      "args": ["build"],
      "group": { "kind": "build", "isDefault": true }
    },
    {
      "label": "test",
      "type": "shell",
      "command": "simple",
      "args": ["test"],
      "group": { "kind": "test", "isDefault": true }
    }
  ]
}
```

### VS Code Debug Controls

| Action | Shortcut |
|--------|----------|
| Start / Continue | F5 |
| Step Over | F10 |
| Step Into | F11 |
| Step Out | Shift+F11 |
| Toggle Breakpoint | F9 |
| Stop | Shift+F5 |
| Restart | Ctrl+Shift+F5 |

### VS Code Breakpoints

- **Line breakpoints**: Click the gutter left of line numbers
- **Conditional breakpoints**: Right-click breakpoint, add condition (e.g., `x > 10 and y < 5`)
- **Log points**: Right-click, add logpoint (e.g., `Value of x is {x}`)
- **Function breakpoints**: Breakpoints pane, "Add Function Breakpoint"

---

## Neovim Setup

### Prerequisites

- Neovim 0.8+
- Plugin manager (lazy.nvim recommended)

### Plugin Installation

Using lazy.nvim (`~/.config/nvim/lua/plugins/lsp.lua`):

```lua
return {
  {
    'neovim/nvim-lspconfig',
    dependencies = {
      'hrsh7th/nvim-cmp',
      'hrsh7th/cmp-nvim-lsp',
      'L3MON4D3/LuaSnip',
    },
    config = function()
      require('lsp-setup')
    end
  },
  {
    'mfussenegger/nvim-dap',
    dependencies = {
      'rcarriga/nvim-dap-ui',
      'theHamsta/nvim-dap-virtual-text',
    },
    config = function()
      require('dap-setup')
    end
  },
}
```

### LSP Configuration

Create `~/.config/nvim/lua/lsp-setup.lua`:

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

if not configs.simple_lsp then
  configs.simple_lsp = {
    default_config = {
      cmd = { 'simple', 'lsp', 'start', '--stdio' },
      filetypes = { 'simple', 'spl' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or
               lspconfig.util.path.dirname(fname)
      end,
    },
  }
end

local capabilities = require('cmp_nvim_lsp').default_capabilities()

lspconfig.simple_lsp.setup {
  capabilities = capabilities,
  on_attach = function(client, bufnr)
    local opts = { buffer = bufnr, noremap = true, silent = true }
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'gD', vim.lsp.buf.declaration, opts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', 'gi', vim.lsp.buf.implementation, opts)
    vim.keymap.set('n', '<C-k>', vim.lsp.buf.signature_help, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
    vim.keymap.set('n', '<leader>rn', vim.lsp.buf.rename, opts)
    vim.keymap.set('n', '<leader>ca', vim.lsp.buf.code_action, opts)
    vim.keymap.set('n', '<leader>f', function()
      vim.lsp.buf.format { async = true }
    end, opts)
    vim.keymap.set('n', '[d', vim.diagnostic.goto_prev, opts)
    vim.keymap.set('n', ']d', vim.diagnostic.goto_next, opts)
    vim.keymap.set('n', '<leader>e', vim.diagnostic.open_float, opts)
    vim.keymap.set('n', '<leader>q', vim.diagnostic.setloclist, opts)
  end,
  flags = { debounce_text_changes = 150 },
}
```

### Autocompletion

Add to `~/.config/nvim/lua/lsp-setup.lua`:

```lua
local cmp = require('cmp')
local luasnip = require('luasnip')

cmp.setup({
  snippet = {
    expand = function(args) luasnip.lsp_expand(args.body) end,
  },
  mapping = cmp.mapping.preset.insert({
    ['<C-b>'] = cmp.mapping.scroll_docs(-4),
    ['<C-f>'] = cmp.mapping.scroll_docs(4),
    ['<C-Space>'] = cmp.mapping.complete(),
    ['<CR>'] = cmp.mapping.confirm({ select = true }),
    ['<Tab>'] = cmp.mapping(function(fallback)
      if cmp.visible() then cmp.select_next_item()
      elseif luasnip.expand_or_jumpable() then luasnip.expand_or_jump()
      else fallback() end
    end, { 'i', 's' }),
  }),
  sources = cmp.config.sources(
    {{ name = 'nvim_lsp' }, { name = 'luasnip' }},
    {{ name = 'buffer' }}
  ),
})
```

### Filetype Detection

Create `~/.config/nvim/ftdetect/simple.vim`:

```vim
au BufRead,BufNewFile *.spl set filetype=simple
au BufRead,BufNewFile *.spipe set filetype=simple
```

Or in Lua (`~/.config/nvim/lua/filetype.lua`):

```lua
vim.filetype.add({
  extension = {
    spl = 'simple',
    spipe = 'simple',
  },
})
```

### DAP Configuration

Create `~/.config/nvim/lua/dap-setup.lua`:

```lua
local dap = require('dap')
local dapui = require('dapui')

dap.adapters.simple = {
  type = 'executable',
  command = 'simple',
  args = { 'dap', 'start', '--stdio' },
}

dap.configurations.simple = {
  {
    type = 'simple',
    request = 'launch',
    name = 'Launch Simple Program',
    program = '${file}',
    cwd = '${workspaceFolder}',
    stopOnEntry = true,
  },
  {
    type = 'simple',
    request = 'launch',
    name = 'Debug Simple Tests',
    program = '${workspaceFolder}/test',
    args = { '--test-runner' },
    cwd = '${workspaceFolder}',
    stopOnEntry = false,
  },
}

dapui.setup()
require('nvim-dap-virtual-text').setup()

-- Auto-open/close DAP UI
dap.listeners.after.event_initialized["dapui_config"] = function() dapui.open() end
dap.listeners.before.event_terminated["dapui_config"] = function() dapui.close() end
dap.listeners.before.event_exited["dapui_config"] = function() dapui.close() end

-- Keybindings
vim.keymap.set('n', '<F5>', dap.continue)
vim.keymap.set('n', '<F10>', dap.step_over)
vim.keymap.set('n', '<F11>', dap.step_into)
vim.keymap.set('n', '<F12>', dap.step_out)
vim.keymap.set('n', '<leader>b', dap.toggle_breakpoint)
vim.keymap.set('n', '<leader>B', function()
  dap.set_breakpoint(vim.fn.input('Breakpoint condition: '))
end)
vim.keymap.set('n', '<leader>dr', dap.repl.open)
vim.keymap.set('n', '<leader>dt', dapui.toggle)
```

---

## DAP Debugging

### DAP Features

- **Breakpoints** -- Line, conditional, function breakpoints
- **Step Execution** -- Step over (F10), step into (F11), step out (Shift+F11/F12)
- **Stack Traces** -- View call stack with file/line information
- **Variable Inspection** -- Inspect local and global variables
- **Pause/Continue** -- Pause and resume execution at any time

### Debugging Workflow

1. Set breakpoints in your `.spl` file
2. Start debugger (F5)
3. Use step controls to walk through code
4. Inspect variables in the Variables pane
5. Use the debug console/REPL to evaluate expressions

### Common Debugging Scenarios

**Nil value:**
```simple
val user = get_user(id)   # Set breakpoint, check if nil
val name = user.name      # May crash if nil
```

**Infinite loop:**
```simple
while condition:           # Set breakpoint, inspect condition
    do_work()
```

**Wrong calculation:**
```simple
val result = calculate(a, b)  # Step into to see intermediate values
```

### Performance Impact

- **Debug mode OFF**: Zero overhead
- **Debug mode ON**: ~5-10% slowdown from location tracking
- **At breakpoint**: No overhead (execution paused)

---

## Troubleshooting

### LSP Not Starting

```bash
# Test server manually
bin/simple lsp
# Should show: "Simple LSP Server starting..."

# Check logs
tail -f .simple/lsp.log
```

**Neovim**: Run `:LspInfo` to check status, `:LspRestart` to restart.

**VS Code**: View -> Output -> select "Simple LSP" from dropdown.

### Completions Not Working

1. Check completion is enabled in config
2. Type `.` after an object to trigger method completion
3. Restart LSP (Neovim: `:LspRestart`, VS Code: Ctrl+Shift+P -> "Reload Window")

### DAP Not Connecting

```bash
# Test DAP adapter
simple dap start --stdio
```

**Neovim**: Enable DAP logging:
```lua
require('dap').set_log_level('TRACE')
:lua vim.cmd('edit ' .. vim.fn.stdpath('cache') .. '/dap.log')
```

**VS Code**: Add `"trace": true` to launch.json configuration.

### Breakpoints Not Hitting

1. Verify breakpoint line has executable code (not comments/blank)
2. Check file path matches exactly (case-sensitive)
3. Ensure debug mode is active
4. Check breakpoint indicator is enabled (red, not gray)

### Diagnostics Slow

Reduce debounce in config:
```sdn
{ diagnostics: { debounce_ms: 100 } }
```

Or disable on-type checking:
```sdn
{ diagnostics: { on_type: false, on_save: true } }
```

---

## Memory and Performance

| Metric | Value |
|--------|-------|
| LSP idle memory | ~10 MB |
| Per-file overhead | ~50 KB |
| 100-file project | ~50 MB |
| 1000-file project | ~200 MB |
| All LSP operations | < 10 ms |

---

## Source Code

- **LSP server**: `src/app/lsp/`
- **DAP server**: `src/app/dap/`
- **LSP tests**: `test/unit/app/lsp/`
- **Debug FFI**: `src/lib/ffi/debug.spl`
