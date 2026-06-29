-- lua/simple/health.lua
-- :checkhealth simple integration
--
-- Checks for the Simple LSP server, tree-sitter queries
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
  vim.health.start("LSP Server")

  local cfg = require("simple").config
  if not cfg then
    vim.health.warn("Plugin not configured yet")
    return
  end

  if not cfg.lsp.enabled then
    vim.health.info("LSP is disabled in config")
    return
  end

  local lsp = require("simple.lsp")
  local cmd, err = lsp._find_server_cmd(vim.fn.getcwd(), cfg.lsp)

  if cmd then
    vim.health.ok("LSP server command found: " .. table.concat(cmd, " "))

    -- Verify the configured LSP command accepts --help without invoking a shell.
    local help_cmd = vim.deepcopy(cmd)
    table.insert(help_cmd, "--help")
    local result = vim.fn.system(help_cmd)
    if vim.v.shell_error == 0 then
      vim.health.ok("LSP command help is available")
    else
      vim.health.warn("LSP command did not accept --help: " .. vim.trim(result))
    end
  else
    vim.health.warn(err)
  end

  -- Check for LSP source directories in the current repository
  local cwd = vim.fn.getcwd()
  local lsp_dirs = {
    "src/lib/gc_sync_mut/lsp",
    "src/lib/gc_async_mut/lsp",
    "src/lib/nogc_sync_mut/lsp",
    "src/lib/nogc_async_mut/lsp",
    "src/app/simple_lsp_mcp",
  }
  local found_source = false
  for _, dir in ipairs(lsp_dirs) do
    if vim.fn.isdirectory(cwd .. "/" .. dir) == 1 then
      vim.health.ok("LSP source directory found: " .. dir)
      found_source = true
    end
  end
  if found_source then
    local handlers = { "hover.spl", "completion.spl", "definition.spl", "references.spl", "semantic_tokens.spl", "diagnostics.spl" }
    local handler_dir = cwd .. "/src/lib/gc_sync_mut/lsp/handlers"
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
    vim.health.info("LSP source directories not found in cwd")
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

  local workspace_cmds = {
    ":SimpleTestWorkspace",
    ":SimpleBreakpointToggle",
    ":SimpleBookmarkToggle",
    ":SimplePointerToggle",
    ":SimplePointerClear",
    ":SimpleBookmarkNext",
    ":SimpleBookmarkPrev",
  }
  local missing = {}
  for _, cmd in ipairs(workspace_cmds) do
    if vim.fn.exists(cmd) ~= 2 then
      table.insert(missing, cmd)
    end
  end
  if #missing == 0 then
    vim.health.ok("Test workspace + editor marker commands available")
  else
    vim.health.warn("Missing commands: " .. table.concat(missing, ", "))
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
  local dirs = { "src/app", "src/core", "src/lib" }
  for _, dir in ipairs(dirs) do
    local path = cwd .. "/" .. dir
    if vim.fn.isdirectory(path) == 1 then
      vim.health.ok("Source directory found: " .. dir)
    end
  end
end

return M
