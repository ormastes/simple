-- lua/simple/lsp.lua
-- LSP server configuration for the Simple language
--
-- The LSP server is implemented in Simple itself at src/app/lsp/server.spl
-- and is started via `simple lsp` or `bin/simple lsp`.
--
-- Server capabilities (handled by src/app/lsp/handlers/):
--   hover.spl          - Hover with math block detection (LaTeX + Unicode pretty text via src/lib/math_repr.spl)
--   completion.spl     - Code completion
--   definition.spl     - Go to definition
--   references.spl     - Find references
--   semantic_tokens.spl - Semantic token highlighting
--   diagnostics.spl    - Diagnostic reporting

local M = {}

---@type SimpleLspConfig
M._config = nil

--- Locate the Simple LSP server binary.
--- The server is started with `simple lsp` (or `bin/simple lsp`).
--- Checks (in order):
---   1. Explicit cmd from config
---   2. bin/simple in the project root
---   3. "simple" on PATH
---@param root_dir string
---@return string[]|nil cmd, string|nil reason
local function find_server_cmd(root_dir, cfg)
  -- If user provided an explicit command, use it
  if cfg.cmd and #cfg.cmd > 0 then
    local bin = cfg.cmd[1]
    -- Resolve relative path against root_dir
    if not vim.startswith(bin, "/") then
      local abs = root_dir .. "/" .. bin
      if vim.fn.executable(abs) == 1 then
        local resolved = vim.deepcopy(cfg.cmd)
        resolved[1] = abs
        return resolved, nil
      end
    end
    if vim.fn.executable(bin) == 1 then
      return cfg.cmd, nil
    end
    return nil, string.format("LSP binary not found: %s", bin)
  end

  -- Try bin/simple in project root
  local project_bin = root_dir .. "/bin/simple"
  if vim.fn.executable(project_bin) == 1 then
    return { project_bin, "lsp" }, nil
  end

  -- Try simple on PATH
  if vim.fn.executable("simple") == 1 then
    return { "simple", "lsp" }, nil
  end

  return nil, "No Simple LSP server found. Install simple or set lsp.cmd in config."
end

--- Find project root directory from a buffer
---@param bufnr integer
---@param markers string[]
---@return string
local function find_root(bufnr, markers)
  local buf_path = vim.api.nvim_buf_get_name(bufnr)
  if buf_path == "" then
    return vim.fn.getcwd()
  end

  -- Use vim.fs.find to locate root markers
  local found = vim.fs.find(markers, {
    path = vim.fs.dirname(buf_path),
    upward = true,
    stop = vim.env.HOME,
  })

  if found and #found > 0 then
    return vim.fs.dirname(found[1])
  end

  return vim.fn.getcwd()
end

--- Default on_attach: set up LSP keymaps
--- The Simple LSP provides: hover (with math block rendering), completion,
--- definition, references, semantic tokens, and diagnostics.
---@param client vim.lsp.Client
---@param bufnr integer
local function default_on_attach(client, bufnr)
  local opts = { buffer = bufnr, silent = true }

  -- Navigation (definition, references handled by src/app/lsp/handlers/)
  vim.keymap.set("n", "gd", vim.lsp.buf.definition, opts)
  vim.keymap.set("n", "gD", vim.lsp.buf.declaration, opts)
  vim.keymap.set("n", "gr", vim.lsp.buf.references, opts)
  vim.keymap.set("n", "gi", vim.lsp.buf.implementation, opts)
  vim.keymap.set("n", "gt", vim.lsp.buf.type_definition, opts)

  -- Information (hover detects m{ } blocks and renders LaTeX + Unicode via math_repr.spl)
  vim.keymap.set("n", "K", vim.lsp.buf.hover, opts)
  vim.keymap.set("n", "<C-k>", vim.lsp.buf.signature_help, opts)
  vim.keymap.set("i", "<C-k>", vim.lsp.buf.signature_help, opts)

  -- Actions
  vim.keymap.set("n", "<leader>rn", vim.lsp.buf.rename, opts)
  vim.keymap.set({ "n", "v" }, "<leader>ca", vim.lsp.buf.code_action, opts)
  vim.keymap.set("n", "<leader>f", function()
    vim.lsp.buf.format({ async = true })
  end, opts)

  -- Diagnostics
  vim.keymap.set("n", "[d", vim.diagnostic.goto_prev, opts)
  vim.keymap.set("n", "]d", vim.diagnostic.goto_next, opts)
  vim.keymap.set("n", "<leader>e", vim.diagnostic.open_float, opts)
  vim.keymap.set("n", "<leader>q", vim.diagnostic.setloclist, opts)

  -- Inlay hints (Neovim 0.10+)
  if client.supports_method("textDocument/inlayHint") then
    if vim.lsp.inlay_hint then
      vim.lsp.inlay_hint.enable(true, { bufnr = bufnr })
    end
  end
end

--- Setup LSP for Simple language files
---@param cfg SimpleLspConfig
function M.setup(cfg)
  M._config = cfg

  -- Use Neovim 0.11+ vim.lsp.config if available, otherwise use autocommand approach
  if vim.lsp.config and vim.lsp.enable then
    -- Neovim 0.11+ native LSP configuration
    vim.lsp.config("simple_ls", {
      cmd = cfg.cmd,
      filetypes = { "simple" },
      root_markers = cfg.root_markers,
      settings = cfg.settings or {},
    })
    vim.lsp.enable("simple_ls")
  else
    -- Neovim 0.9/0.10 fallback: use vim.lsp.start in an autocommand
    vim.api.nvim_create_autocmd("FileType", {
      group = vim.api.nvim_create_augroup("simple_lsp", { clear = true }),
      pattern = "simple",
      callback = function(ev)
        local bufnr = ev.buf
        local root_dir = find_root(bufnr, cfg.root_markers)
        local cmd, err = find_server_cmd(root_dir, cfg)

        if not cmd then
          -- Silently skip -- :checkhealth will report this
          return
        end

        vim.lsp.start({
          name = "simple_ls",
          cmd = cmd,
          root_dir = root_dir,
          settings = cfg.settings or {},
          capabilities = M._make_capabilities(),
          on_attach = function(client, buf)
            default_on_attach(client, buf)
            if cfg.on_attach then
              cfg.on_attach(client, buf)
            end
          end,
        })
      end,
    })
  end
end

--- Build LSP client capabilities, incorporating cmp-nvim-lsp if available
---@return table
function M._make_capabilities()
  local capabilities = vim.lsp.protocol.make_client_capabilities()

  -- Integrate with nvim-cmp if available
  local ok, cmp_lsp = pcall(require, "cmp_nvim_lsp")
  if ok then
    capabilities = vim.tbl_deep_extend("force", capabilities, cmp_lsp.default_capabilities())
  end

  return capabilities
end

--- Restart the Simple LSP server for the current buffer
function M.restart()
  local clients = vim.lsp.get_clients({ name = "simple_ls" })
  for _, client in ipairs(clients) do
    local bufs = vim.lsp.get_buffers_by_client_id(client.id)
    client.stop()
    vim.defer_fn(function()
      for _, buf in ipairs(bufs) do
        if vim.api.nvim_buf_is_valid(buf) then
          -- Re-trigger FileType to restart
          vim.api.nvim_buf_call(buf, function()
            vim.cmd("edit")
          end)
        end
      end
    end, 500)
  end
end

--- Show LSP log file
function M.show_log()
  local log_path = vim.lsp.get_log_path()
  if vim.fn.filereadable(log_path) == 1 then
    vim.cmd("split " .. vim.fn.fnameescape(log_path))
    vim.cmd("normal! G")
  else
    vim.notify("No LSP log file found at: " .. log_path, vim.log.levels.WARN)
  end
end

return M
