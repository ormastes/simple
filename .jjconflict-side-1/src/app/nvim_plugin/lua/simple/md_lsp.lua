-- lua/simple/md_lsp.lua
-- LSP server configuration for the Markdown language
--
-- The LSP server is implemented in Simple at src/app/md_lsp/md_lsp_main.spl
-- and is started via `bin/simple run src/app/md_lsp/md_lsp_main.spl`.

local M = {}

---@type SimpleMdLspConfig
M._config = nil

--- Locate the Markdown LSP server command.
--- Checks (in order):
---   1. Explicit cmd from config
---   2. bin/simple in the project root
---   3. "simple" on PATH
---@param root_dir string
---@param cfg table
---@return string[]|nil cmd, string|nil reason
local function find_server_cmd(root_dir, cfg)
  -- If user provided an explicit command, use it
  if cfg.cmd and #cfg.cmd > 0 then
    local bin = cfg.cmd[1]
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
    return nil, string.format("Markdown LSP binary not found: %s", bin)
  end

  -- Try bin/simple in project root
  local project_bin = root_dir .. "/bin/simple"
  if vim.fn.executable(project_bin) == 1 then
    return { project_bin, "run", "src/app/md_lsp/md_lsp_main.spl" }, nil
  end

  -- Try simple on PATH
  if vim.fn.executable("simple") == 1 then
    return { "simple", "run", "src/app/md_lsp/md_lsp_main.spl" }, nil
  end

  return nil, "No Markdown LSP server found. Install simple or set md_lsp.cmd in config."
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

--- Default on_attach: set up LSP keymaps for markdown buffers
---@param client vim.lsp.Client
---@param bufnr integer
local function default_on_attach(client, bufnr)
  local opts = { buffer = bufnr, silent = true }

  -- Information
  vim.keymap.set("n", "K", vim.lsp.buf.hover, opts)
  vim.keymap.set("n", "<C-k>", vim.lsp.buf.signature_help, opts)

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
end

--- Build LSP client capabilities, incorporating cmp-nvim-lsp if available
---@return table
function M._make_capabilities()
  local capabilities = vim.lsp.protocol.make_client_capabilities()

  local ok, cmp_lsp = pcall(require, "cmp_nvim_lsp")
  if ok then
    capabilities = vim.tbl_deep_extend("force", capabilities, cmp_lsp.default_capabilities())
  end

  return capabilities
end

--- Setup LSP for Markdown files
---@param cfg table
function M.setup(cfg)
  M._config = cfg

  -- Use Neovim 0.11+ vim.lsp.config if available, otherwise use autocommand approach
  if vim.lsp.config and vim.lsp.enable then
    vim.lsp.config("md_ls", {
      cmd = cfg.cmd,
      filetypes = { "markdown" },
      root_markers = cfg.root_markers,
      settings = cfg.settings or {},
    })
    vim.lsp.enable("md_ls")
  else
    -- Neovim 0.9/0.10 fallback: use vim.lsp.start in an autocommand
    vim.api.nvim_create_autocmd("FileType", {
      group = vim.api.nvim_create_augroup("md_lsp", { clear = true }),
      pattern = "markdown",
      callback = function(ev)
        local bufnr = ev.buf
        local root_dir = find_root(bufnr, cfg.root_markers)
        local cmd, err = find_server_cmd(root_dir, cfg)

        if not cmd then
          -- Silently skip -- :checkhealth will report this
          return
        end

        vim.lsp.start({
          name = "md_ls",
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

--- Restart the Markdown LSP server for the current buffer
function M.restart()
  local clients = vim.lsp.get_clients({ name = "md_ls" })
  for _, client in ipairs(clients) do
    local bufs = vim.lsp.get_buffers_by_client_id(client.id)
    client.stop()
    vim.defer_fn(function()
      for _, buf in ipairs(bufs) do
        if vim.api.nvim_buf_is_valid(buf) then
          vim.api.nvim_buf_call(buf, function()
            vim.cmd("edit")
          end)
        end
      end
    end, 500)
  end
end

return M
