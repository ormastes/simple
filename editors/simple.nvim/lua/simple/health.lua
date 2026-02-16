-- lua/simple/health.lua
-- :checkhealth simple integration
--
-- Checks for the Simple LSP server (src/app/lsp/), tree-sitter queries
-- (src/compiler/parser/treesitter/queries/), and project structure.

local M = {}

function M.check()
  vim.health.start("simple.nvim")

  -- Check Neovim version
  local nvim_version = vim.version()
  if nvim_version.major > 0 or (nvim_version.major == 0 and nvim_version.minor >= 9) then
    vim.health.ok(
      string.format("Neovim version: %d.%d.%d (>= 0.9 required)", nvim_version.major, nvim_version.minor, nvim_version.patch)
    )
  else
    vim.health.error(
      string.format(
        "Neovim version %d.%d.%d is too old. simple.nvim requires >= 0.9",
        nvim_version.major,
        nvim_version.minor,
        nvim_version.patch
      )
    )
  end

  -- Check if plugin is initialized
  local simple = require("simple")
  if simple._initialized then
    vim.health.ok("simple.nvim is initialized (setup() has been called)")
  else
    vim.health.warn("simple.nvim has not been initialized. Call require('simple').setup() in your config.")
  end

  -- Check LSP server binary
  M._check_lsp()

  -- Check tree-sitter parser
  M._check_treesitter()

  -- Check math rendering
  M._check_math()

  -- Check project structure
  M._check_project()
end

function M._check_lsp()
  vim.health.start("LSP Server (src/app/lsp/)")

  local cfg = require("simple").config
  if not cfg then
    vim.health.warn("Plugin not configured yet")
    return
  end

  if not cfg.lsp.enabled then
    vim.health.info("LSP is disabled in config")
    return
  end

  -- Check if `simple lsp` binary exists
  local cmd = cfg.lsp.cmd
  if cmd and #cmd > 0 then
    local bin = cmd[1]

    -- Try absolute/relative path
    if vim.fn.executable(bin) == 1 then
      vim.health.ok("LSP server binary found: " .. bin)
    else
      -- Try in project root
      local project_bin = vim.fn.getcwd() .. "/" .. bin
      if vim.fn.executable(project_bin) == 1 then
        vim.health.ok("LSP server binary found at: " .. project_bin)
      else
        vim.health.warn(
          string.format("LSP server binary not found: %s (will search PATH on startup)", bin)
        )
      end
    end
  end

  -- Verify `simple lsp` subcommand works
  local lsp_bin = nil
  if cmd and #cmd > 0 then
    lsp_bin = cmd[1]
    if not vim.startswith(lsp_bin, "/") then
      local abs = vim.fn.getcwd() .. "/" .. lsp_bin
      if vim.fn.executable(abs) == 1 then
        lsp_bin = abs
      end
    end
  else
    local project_bin = vim.fn.getcwd() .. "/bin/simple"
    if vim.fn.executable(project_bin) == 1 then
      lsp_bin = project_bin
    elseif vim.fn.executable("simple") == 1 then
      lsp_bin = "simple"
    end
  end

  if lsp_bin and vim.fn.executable(lsp_bin) == 1 then
    local result = vim.fn.system({ lsp_bin, "lsp", "--help" })
    if vim.v.shell_error == 0 then
      vim.health.ok("`" .. lsp_bin .. " lsp` subcommand is available")
    else
      vim.health.warn("`" .. lsp_bin .. " lsp` subcommand not found. Update your Simple binary.")
    end
  end

  -- Check for src/app/lsp/ directory (the LSP implementation)
  local cwd = vim.fn.getcwd()
  local lsp_dir = cwd .. "/src/app/lsp"
  if vim.fn.isdirectory(lsp_dir) == 1 then
    vim.health.ok("LSP implementation found at: src/app/lsp/")

    -- Check for key handler files
    local handlers = { "hover.spl", "completion.spl", "definition.spl", "references.spl", "semantic_tokens.spl", "diagnostics.spl" }
    local handler_dir = lsp_dir .. "/handlers"
    if vim.fn.isdirectory(handler_dir) == 1 then
      for _, h in ipairs(handlers) do
        local hpath = handler_dir .. "/" .. h
        if vim.fn.filereadable(hpath) == 1 then
          vim.health.ok("  handler: " .. h)
        else
          vim.health.warn("  handler missing: " .. h)
        end
      end
    end
  else
    vim.health.info("LSP source directory (src/app/lsp/) not found in cwd")
  end

  -- Check if LSP is currently running
  local clients = vim.lsp.get_clients({ name = "simple_ls" })
  if #clients > 0 then
    for _, client in ipairs(clients) do
      vim.health.ok(string.format("LSP server running (client id: %d, pid: %s)", client.id, tostring(client.rpc and client.rpc.pid)))
    end
  else
    vim.health.info("No LSP server currently running (will start when opening a .spl file)")
  end
end

function M._check_treesitter()
  vim.health.start("Tree-sitter")

  local ts = require("simple.treesitter")
  if ts.is_parser_available() then
    vim.health.ok("Tree-sitter parser for Simple is installed")
  else
    vim.health.warn(
      "Tree-sitter parser for Simple is not installed. "
        .. "Install with :TSInstall simple (if using nvim-treesitter) "
        .. "or build from source."
    )
  end

  -- Check query files (expected at src/compiler/parser/treesitter/queries/)
  local query_path = ts.get_query_path()
  if query_path then
    vim.health.ok("Tree-sitter queries found at: " .. query_path)

    -- Verify individual query files
    local expected = { "highlights.scm", "folds.scm", "indents.scm", "locals.scm", "textobjects.scm", "injections.scm" }
    for _, name in ipairs(expected) do
      local path = query_path .. "/" .. name
      if vim.fn.filereadable(path) == 1 then
        vim.health.ok("  " .. name .. " found")
      else
        vim.health.warn("  " .. name .. " not found at " .. path)
      end
    end
  else
    vim.health.info("Tree-sitter query directory not found in project (using bundled queries if available)")
  end
end

function M._check_math()
  vim.health.start("Math Rendering")

  local cfg = require("simple").config
  if not cfg then
    return
  end

  if cfg.math.enabled then
    vim.health.ok("Math block detection: enabled")
  else
    vim.health.info("Math block detection: disabled")
  end

  if cfg.math.conceal then
    vim.health.ok("Math conceal: enabled (conceals m{ } delimiters)")
  else
    vim.health.info("Math conceal: disabled")
  end

  if cfg.math.float_on_hover then
    vim.health.ok("Math float on hover: enabled")
  else
    vim.health.info("Math float on hover: disabled")
  end

  vim.health.info(string.format("Math update delay: %d ms", cfg.math.update_delay))
end

function M._check_project()
  vim.health.start("Project Detection")

  local cwd = vim.fn.getcwd()

  -- Check for simple.sdn
  if vim.fn.filereadable(cwd .. "/simple.sdn") == 1 then
    vim.health.ok("simple.sdn found in: " .. cwd)
  else
    vim.health.info("No simple.sdn found in cwd (not a Simple project root?)")
  end

  -- Check for bin/simple
  local bin_simple = cwd .. "/bin/simple"
  if vim.fn.executable(bin_simple) == 1 then
    vim.health.ok("Simple binary found at: " .. bin_simple)
  else
    vim.health.info("No bin/simple found in cwd")
  end

  -- Check for source directories
  local dirs = { "src/std", "src/app", "src/core", "src/lib" }
  for _, dir in ipairs(dirs) do
    local path = cwd .. "/" .. dir
    if vim.fn.isdirectory(path) == 1 then
      vim.health.ok("Source directory found: " .. dir)
    end
  end
end

return M
