-- plugin/simple.lua
-- Auto-loaded plugin entry point for simple.nvim
-- Sets up autocommands and commands that work before setup() is called

-- Guard against double-loading
if vim.g.loaded_simple_nvim then
  return
end
vim.g.loaded_simple_nvim = true

-- Ensure filetype detection is registered even before setup()
vim.filetype.add({
  extension = {
    spl = "simple",
  },
})

-- Create autocommand group for plugin-level events
local group = vim.api.nvim_create_augroup("simple_nvim_plugin", { clear = true })

-- Auto-setup conceallevel for Simple files
vim.api.nvim_create_autocmd("FileType", {
  group = group,
  pattern = "simple",
  callback = function()
    -- Set conceallevel for math block rendering
    if vim.wo.conceallevel < 2 then
      vim.wo.conceallevel = 2
    end
    vim.wo.signcolumn = "yes"
    -- Reveal conceal on cursor line in normal mode
    vim.wo.concealcursor = ""
  end,
})

-- Diagnostic configuration for Simple files
vim.api.nvim_create_autocmd("FileType", {
  group = group,
  pattern = "simple",
  once = true,
  callback = function()
    -- Configure diagnostics display
    vim.diagnostic.config({
      float = {
        border = "rounded",
        source = "if_many",
        focusable = true,
      },
      virtual_text = {
        prefix = "●",
        spacing = 2,
      },
      signs = {
        text = {
          [vim.diagnostic.severity.ERROR] = "✘",
          [vim.diagnostic.severity.WARN] = "▲",
          [vim.diagnostic.severity.INFO] = "i",
          [vim.diagnostic.severity.HINT] = "↳",
        },
      },
      underline = true,
      update_in_insert = false,
      severity_sort = true,
    })
  end,
})
