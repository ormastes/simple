-- lua/simple/config.lua
-- Default configuration for simple.nvim

local M = {}

---@class SimpleConfig
---@field lsp SimpleLspConfig
---@field math SimpleMathConfig
---@field treesitter SimpleTreesitterConfig
---@field commands SimpleCommandsConfig
---@field keymaps SimpleKeymapsConfig

---@class SimpleLspConfig
---@field enabled boolean
---@field cmd string[]
---@field root_markers string[]
---@field settings table
---@field on_attach? fun(client: vim.lsp.Client, bufnr: integer)

---@class SimpleMathConfig
---@field enabled boolean
---@field conceal boolean
---@field float_on_hover boolean
---@field update_delay integer
---@field highlight_group string

---@class SimpleTreesitterConfig
---@field ensure_installed boolean
---@field query_path? string

---@class SimpleCommandsConfig
---@field enabled boolean
---@field test_cmd string[]

---@class SimpleKeymapsConfig
---@field enabled boolean
---@field prefix string

---@type SimpleConfig
M.defaults = {
  lsp = {
    enabled = true,
    cmd = { "simple", "lsp" },
    root_markers = { "simple.sdn", ".git" },
    settings = {},
    on_attach = nil,
  },
  math = {
    enabled = true,
    conceal = true,
    float_on_hover = true,
    update_delay = 100,
    highlight_group = "SimpleMathBlock",
  },
  treesitter = {
    ensure_installed = true,
    query_path = nil, -- auto-detect from project
  },
  commands = {
    enabled = true,
    test_cmd = { "bin/simple", "test" },
  },
  keymaps = {
    enabled = true,
    prefix = "<localleader>s",
  },
}

--- Deep merge two tables, with overrides taking precedence
---@param base table
---@param overrides table
---@return table
function M.merge(base, overrides)
  local result = vim.deepcopy(base)
  if not overrides then
    return result
  end
  for k, v in pairs(overrides) do
    if type(v) == "table" and type(result[k]) == "table" then
      result[k] = M.merge(result[k], v)
    else
      result[k] = v
    end
  end
  return result
end

return M
