# Neovim Setup Guide: Simple LSP and DAP

**Complete guide for setting up Simple language support in Neovim with native LSP and DAP**

---

## Prerequisites

- ✅ Neovim 0.8+ (`nvim --version`)
- ✅ Simple compiler installed and in PATH
- ✅ Plugin manager (lazy.nvim, packer, or vim-plug)
- ✅ Basic Lua knowledge

---

## Part 1: LSP Setup (Code Intelligence)

### Step 1: Install Required Plugins

Using **lazy.nvim** (`~/.config/nvim/lua/plugins/lsp.lua`):

```lua
return {
  -- LSP Configuration
  {
    'neovim/nvim-lspconfig',
    dependencies = {
      'williamboman/mason.nvim',
      'williamboman/mason-lspconfig.nvim',
      'hrsh7th/nvim-cmp',  -- Autocompletion
      'hrsh7th/cmp-nvim-lsp',
      'L3MON4D3/LuaSnip',
    },
    config = function()
      require('lsp-setup')
    end
  },

  -- DAP (Debug Adapter Protocol)
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

  -- Nice UI improvements
  {
    'nvim-telescope/telescope.nvim',
    dependencies = { 'nvim-lua/plenary.nvim' }
  },
}
```

### Step 2: Configure Simple LSP

Create `~/.config/nvim/lua/lsp-setup.lua`:

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Define Simple LSP server if not already defined
if not configs.simple_lsp then
  configs.simple_lsp = {
    default_config = {
      cmd = { 'simple', 'lsp', 'start', '--stdio' },
      filetypes = { 'simple', 'spl' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or
               lspconfig.util.path.dirname(fname)
      end,
      settings = {},
    },
  }
end

-- Setup Simple LSP with capabilities
local capabilities = require('cmp_nvim_lsp').default_capabilities()

lspconfig.simple_lsp.setup {
  capabilities = capabilities,
  on_attach = function(client, bufnr)
    -- Keybindings
    local opts = { buffer = bufnr, noremap = true, silent = true }

    -- Go to definition
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)

    -- Go to declaration
    vim.keymap.set('n', 'gD', vim.lsp.buf.declaration, opts)

    -- Hover information
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)

    -- Implementation
    vim.keymap.set('n', 'gi', vim.lsp.buf.implementation, opts)

    -- Signature help
    vim.keymap.set('n', '<C-k>', vim.lsp.buf.signature_help, opts)

    -- Find references
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)

    -- Rename symbol
    vim.keymap.set('n', '<leader>rn', vim.lsp.buf.rename, opts)

    -- Code action
    vim.keymap.set('n', '<leader>ca', vim.lsp.buf.code_action, opts)

    -- Format
    vim.keymap.set('n', '<leader>f', function()
      vim.lsp.buf.format { async = true }
    end, opts)

    -- Diagnostics
    vim.keymap.set('n', '[d', vim.diagnostic.goto_prev, opts)
    vim.keymap.set('n', ']d', vim.diagnostic.goto_next, opts)
    vim.keymap.set('n', '<leader>e', vim.diagnostic.open_float, opts)
    vim.keymap.set('n', '<leader>q', vim.diagnostic.setloclist, opts)

    -- Document symbols with Telescope
    vim.keymap.set('n', '<leader>ds', ':Telescope lsp_document_symbols<CR>', opts)

    -- Workspace symbols
    vim.keymap.set('n', '<leader>ws', ':Telescope lsp_workspace_symbols<CR>', opts)

    -- Auto-format on save
    if client.server_capabilities.documentFormattingProvider then
      vim.api.nvim_create_autocmd('BufWritePre', {
        buffer = bufnr,
        callback = function()
          vim.lsp.buf.format { async = false }
        end,
      })
    end

    print('Simple LSP attached to buffer ' .. bufnr)
  end,
  flags = {
    debounce_text_changes = 150,
  },
  settings = {
    simple = {
      diagnostics = {
        enable = true,
      },
    },
  },
}
```

### Step 3: Configure Autocompletion

Add to `~/.config/nvim/lua/lsp-setup.lua`:

```lua
-- Setup nvim-cmp
local cmp = require('cmp')
local luasnip = require('luasnip')

cmp.setup({
  snippet = {
    expand = function(args)
      luasnip.lsp_expand(args.body)
    end,
  },
  mapping = cmp.mapping.preset.insert({
    ['<C-b>'] = cmp.mapping.scroll_docs(-4),
    ['<C-f>'] = cmp.mapping.scroll_docs(4),
    ['<C-Space>'] = cmp.mapping.complete(),
    ['<C-e>'] = cmp.mapping.abort(),
    ['<CR>'] = cmp.mapping.confirm({ select = true }),
    ['<Tab>'] = cmp.mapping(function(fallback)
      if cmp.visible() then
        cmp.select_next_item()
      elseif luasnip.expand_or_jumpable() then
        luasnip.expand_or_jump()
      else
        fallback()
      end
    end, { 'i', 's' }),
    ['<S-Tab>'] = cmp.mapping(function(fallback)
      if cmp.visible() then
        cmp.select_prev_item()
      elseif luasnip.jumpable(-1) then
        luasnip.jump(-1)
      else
        fallback()
      end
    end, { 'i', 's' }),
  }),
  sources = cmp.config.sources({
    { name = 'nvim_lsp' },
    { name = 'luasnip' },
  }, {
    { name = 'buffer' },
  }),
})
```

### Step 4: Configure File Detection

Add to `~/.config/nvim/ftdetect/simple.vim`:

```vim
au BufRead,BufNewFile *.spl set filetype=simple
au BufRead,BufNewFile *.sspec set filetype=simple
```

Or in Lua (`~/.config/nvim/lua/filetype.lua`):

```lua
vim.filetype.add({
  extension = {
    spl = 'simple',
    sspec = 'simple',
  },
})
```

### Step 5: Syntax Highlighting

Create `~/.config/nvim/after/syntax/simple.vim`:

```vim
" Simple language syntax highlighting

if exists("b:current_syntax")
  finish
endif

" Keywords
syntax keyword simpleKeyword fn val var class struct enum trait impl
syntax keyword simpleKeyword import export from as
syntax keyword simpleKeyword if elif else match case
syntax keyword simpleKeyword while for loop break continue return
syntax keyword simpleKeyword me self static

" Types
syntax keyword simpleType i8 i16 i32 i64 u8 u16 u32 u64
syntax keyword simpleType f32 f64 bool text
syntax keyword simpleType Option Result Some None Ok Err

" Constants
syntax keyword simpleConstant true false nil

" Comments
syntax match simpleComment "#.*$"

" Strings
syntax region simpleString start=/"/ skip=/\\"/ end=/"/
syntax region simpleString start=/'/ skip=/\\'/ end=/'/

" Numbers
syntax match simpleNumber "\<\d\+\>"
syntax match simpleFloat "\<\d\+\.\d\+\>"

" Operators
syntax match simpleOperator "+\|-\|*\|/\|%\|=\|<\|>\|&\||\|!\|?"

" Highlighting
highlight link simpleKeyword Keyword
highlight link simpleType Type
highlight link simpleConstant Constant
highlight link simpleComment Comment
highlight link simpleString String
highlight link simpleNumber Number
highlight link simpleFloat Float
highlight link simpleOperator Operator

let b:current_syntax = "simple"
```

---

## Part 2: DAP Setup (Debugging)

### Step 1: Configure DAP

Create `~/.config/nvim/lua/dap-setup.lua`:

```lua
local dap = require('dap')
local dapui = require('dapui')

-- Simple DAP adapter configuration
dap.adapters.simple = {
  type = 'executable',
  command = 'simple',
  args = { 'dap', 'start', '--stdio' },
}

-- Simple DAP configuration
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
    name = 'Launch Simple Program (No Stop)',
    program = '${file}',
    cwd = '${workspaceFolder}',
    stopOnEntry = false,
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

-- DAP UI setup
dapui.setup({
  icons = { expanded = "▾", collapsed = "▸" },
  mappings = {
    expand = { "<CR>", "<2-LeftMouse>" },
    open = "o",
    remove = "d",
    edit = "e",
    repl = "r",
    toggle = "t",
  },
  layouts = {
    {
      elements = {
        { id = "scopes", size = 0.25 },
        { id = "breakpoints", size = 0.25 },
        { id = "stacks", size = 0.25 },
        { id = "watches", size = 0.25 },
      },
      size = 40,
      position = "left",
    },
    {
      elements = {
        { id = "repl", size = 0.5 },
        { id = "console", size = 0.5 },
      },
      size = 10,
      position = "bottom",
    },
  },
})

-- Virtual text setup
require('nvim-dap-virtual-text').setup()

-- Auto-open/close DAP UI
dap.listeners.after.event_initialized["dapui_config"] = function()
  dapui.open()
end
dap.listeners.before.event_terminated["dapui_config"] = function()
  dapui.close()
end
dap.listeners.before.event_exited["dapui_config"] = function()
  dapui.close()
end

-- Keybindings
vim.keymap.set('n', '<F5>', dap.continue, { desc = 'Debug: Continue' })
vim.keymap.set('n', '<F10>', dap.step_over, { desc = 'Debug: Step Over' })
vim.keymap.set('n', '<F11>', dap.step_into, { desc = 'Debug: Step Into' })
vim.keymap.set('n', '<F12>', dap.step_out, { desc = 'Debug: Step Out' })
vim.keymap.set('n', '<leader>b', dap.toggle_breakpoint, { desc = 'Debug: Toggle Breakpoint' })
vim.keymap.set('n', '<leader>B', function()
  dap.set_breakpoint(vim.fn.input('Breakpoint condition: '))
end, { desc = 'Debug: Set Conditional Breakpoint' })
vim.keymap.set('n', '<leader>dr', dap.repl.open, { desc = 'Debug: Open REPL' })
vim.keymap.set('n', '<leader>dl', dap.run_last, { desc = 'Debug: Run Last' })
vim.keymap.set('n', '<leader>dt', dapui.toggle, { desc = 'Debug: Toggle UI' })
```

### Step 2: Breakpoint Signs

Add to your init.lua:

```lua
vim.fn.sign_define('DapBreakpoint', {
  text = '🔴',
  texthl = 'DapBreakpoint',
  linehl = '',
  numhl = 'DapBreakpoint'
})

vim.fn.sign_define('DapBreakpointCondition', {
  text = '🟡',
  texthl = 'DapBreakpoint',
  linehl = '',
  numhl = 'DapBreakpoint'
})

vim.fn.sign_define('DapStopped', {
  text = '▶️',
  texthl = 'DapStopped',
  linehl = 'DapStoppedLine',
  numhl = 'DapStopped'
})
```

---

## Part 3: Complete Configuration

### Minimal init.lua

```lua
-- Set leader key
vim.g.mapleader = ' '
vim.g.maplocalleader = ' '

-- Basic settings
vim.opt.number = true
vim.opt.relativenumber = true
vim.opt.signcolumn = 'yes'
vim.opt.updatetime = 250
vim.opt.timeoutlen = 300

-- Install lazy.nvim plugin manager
local lazypath = vim.fn.stdpath('data') .. '/lazy/lazy.nvim'
if not vim.loop.fs_stat(lazypath) then
  vim.fn.system({
    'git',
    'clone',
    '--filter=blob:none',
    'https://github.com/folke/lazy.nvim.git',
    '--branch=stable',
    lazypath,
  })
end
vim.opt.rtp:prepend(lazypath)

-- Load plugins
require('lazy').setup('plugins')

-- File type detection
vim.filetype.add({
  extension = {
    spl = 'simple',
    sspec = 'simple',
  },
})

-- LSP and DAP setup
require('lsp-setup')
require('dap-setup')
```

---

## Usage Guide

### LSP Features

**Auto-completion**:
- Start typing and press `<C-Space>` to trigger
- Use `<Tab>` and `<S-Tab>` to navigate
- Press `<CR>` to select

**Go to Definition**:
- Place cursor on symbol
- Press `gd` to jump to definition
- Press `<C-o>` to jump back

**Hover Information**:
- Place cursor on symbol
- Press `K` to show hover info

**Find References**:
- Place cursor on symbol
- Press `gr` to show all references
- Use quickfix list to navigate

**Diagnostics**:
- Press `]d` / `[d` to jump between errors
- Press `<leader>e` to show error details
- Press `<leader>q` to open diagnostics list

**Document Symbols**:
- Press `<leader>ds` to see symbol outline
- Use Telescope to search and navigate

### DAP Features

**Start Debugging**:
```
:lua require('dap').continue()
```
Or press `<F5>`

**Set Breakpoints**:
- Press `<leader>b` on line
- Press `<leader>B` for conditional breakpoint

**Debug Controls**:
- `<F5>`: Continue
- `<F10>`: Step over
- `<F11>`: Step into
- `<F12>`: Step out

**Inspect Variables**:
- Variables appear in left sidebar
- Hover over variable in code to see value
- Use REPL to evaluate expressions

**REPL Commands**:
```
:lua require('dap').repl.open()
```

In REPL:
```
> x + y
> myFunction(42)
```

---

## Advanced Configuration

### Telescope Integration

```lua
-- Add to keybindings
vim.keymap.set('n', '<leader>ff', ':Telescope find_files<CR>')
vim.keymap.set('n', '<leader>fg', ':Telescope live_grep<CR>')
vim.keymap.set('n', '<leader>fb', ':Telescope buffers<CR>')
vim.keymap.set('n', '<leader>fh', ':Telescope help_tags<CR>')

-- LSP specific
vim.keymap.set('n', '<leader>fd', ':Telescope lsp_definitions<CR>')
vim.keymap.set('n', '<leader>fr', ':Telescope lsp_references<CR>')
vim.keymap.set('n', '<leader>fs', ':Telescope lsp_document_symbols<CR>')
```

### Auto-commands

```lua
-- Auto-format on save
vim.api.nvim_create_autocmd('BufWritePre', {
  pattern = '*.spl',
  callback = function()
    vim.lsp.buf.format { async = false }
  end,
})

-- Highlight on yank
vim.api.nvim_create_autocmd('TextYankPost', {
  callback = function()
    vim.highlight.on_yank()
  end,
})
```

### Custom Commands

```lua
-- Debug current file
vim.api.nvim_create_user_command('DebugFile', function()
  require('dap').continue()
end, {})

-- Run tests in debug mode
vim.api.nvim_create_user_command('DebugTest', function()
  local dap = require('dap')
  dap.run(dap.configurations.simple[3])  -- Test configuration
end, {})
```

---

## Troubleshooting

### LSP Not Starting

**Check LSP status**:
```vim
:LspInfo
```

**Check logs**:
```vim
:lua vim.cmd('edit ' .. vim.lsp.get_log_path())
```

**Manual test**:
```bash
simple lsp start --stdio
```

### Completion Not Working

**Check capabilities**:
```lua
:lua print(vim.inspect(vim.lsp.get_active_clients()[1].server_capabilities))
```

**Restart LSP**:
```vim
:LspRestart
```

### DAP Not Connecting

**Check DAP status**:
```lua
:lua print(vim.inspect(require('dap').configurations))
```

**Enable DAP logging**:
```lua
require('dap').set_log_level('TRACE')
:lua vim.cmd('edit ' .. vim.fn.stdpath('cache') .. '/dap.log')
```

---

## Tips and Tricks

### 1. Use Which-Key for Keybinding Help

```lua
{
  'folke/which-key.nvim',
  config = function()
    require('which-key').setup()
  end
}
```

### 2. Better Diagnostics with Trouble

```lua
{
  'folke/trouble.nvim',
  config = function()
    require('trouble').setup()
  end
}
```

### 3. Git Integration

```lua
{
  'lewis6991/gitsigns.nvim',
  config = function()
    require('gitsigns').setup()
  end
}
```

### 4. File Explorer

```lua
{
  'nvim-tree/nvim-tree.lua',
  config = function()
    require('nvim-tree').setup()
  end
}
```

---

## Resources

- **Neovim LSP Docs**: `:help lsp`
- **DAP Docs**: `:help dap`
- **Simple Docs**: `simple --help lsp`
- **Community**: Neovim Discord, Reddit r/neovim

---

**Status**: ✅ Complete Neovim setup guide for Simple LSP and DAP
