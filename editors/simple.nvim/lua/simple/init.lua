-- lua/simple/init.lua
-- Main entry point for simple.nvim - Neovim plugin for the Simple language

local M = {}

M.version = "0.1.0"

---@type SimpleConfig
M.config = nil

--- Whether setup() has been called
M._initialized = false

--- Setup simple.nvim with user options
---@param opts? table User configuration overrides
function M.setup(opts)
  local config_mod = require("simple.config")
  M.config = config_mod.merge(config_mod.defaults, opts or {})

  -- Define highlight groups before anything uses them
  M._setup_highlights()

  -- Initialize subsystems
  if M.config.treesitter.ensure_installed then
    require("simple.treesitter").setup(M.config.treesitter)
  end

  if M.config.lsp.enabled then
    require("simple.lsp").setup(M.config.lsp)
  end

  if M.config.math.enabled then
    require("simple.math").setup(M.config.math)
  end

  if M.config.commands.enabled then
    require("simple.commands").setup(M.config)
  end

  M._initialized = true
end

--- Define default highlight groups
function M._setup_highlights()
  local hl = vim.api.nvim_set_hl

  -- Math block highlighting
  hl(0, "SimpleMathBlock", { link = "Special", default = true })
  hl(0, "SimpleMathDelimiter", { link = "Delimiter", default = true })
  hl(0, "SimpleMathContent", { link = "String", default = true })

  -- Float window
  hl(0, "SimpleMathFloat", { link = "NormalFloat", default = true })
  hl(0, "SimpleMathFloatBorder", { link = "FloatBorder", default = true })
  hl(0, "SimpleMathFloatTitle", { link = "Title", default = true })

  -- Test output
  hl(0, "SimpleTestPass", { fg = "#a6e3a1", default = true })
  hl(0, "SimpleTestFail", { fg = "#f38ba8", default = true })
  hl(0, "SimpleTestPending", { fg = "#f9e2af", default = true })

  -- Operator highlights
  hl(0, "SimplePipeOperator", { link = "Operator", default = true })
  hl(0, "SimpleComposeOperator", { link = "Operator", default = true })
  hl(0, "SimpleLayerConnect", { link = "Operator", default = true })
end

return M
