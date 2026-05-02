-- lua/simple/commands.lua
-- User commands for Simple language development

local M = {}

---@type SimpleConfig
M._config = nil

--- Setup user commands
---@param cfg SimpleConfig
function M.setup(cfg)
  M._config = cfg

  -- :SimpleTest [file] - run tests
  vim.api.nvim_create_user_command("SimpleTest", function(cmd_opts)
    M.run_test(cmd_opts.args)
  end, {
    nargs = "?",
    complete = "file",
    desc = "Run Simple tests (current file or specified path)",
  })

  -- :SimpleBrief - activate brief view (fold all to signatures)
  vim.api.nvim_create_user_command("SimpleBrief", function()
    M.brief_view()
  end, {
    desc = "Collapse all folds to show only signatures",
  })

  -- :SimpleBriefExpand - expand all folds
  vim.api.nvim_create_user_command("SimpleBriefExpand", function()
    vim.cmd("normal! zR")
    vim.notify("Simple Brief View: all code expanded.", vim.log.levels.INFO)
  end, {
    desc = "Expand all folds",
  })

  -- :SimpleLspRestart - restart LSP server
  vim.api.nvim_create_user_command("SimpleLspRestart", function()
    require("simple.lsp").restart()
    vim.notify("Simple LSP server restarting...", vim.log.levels.INFO)
  end, {
    desc = "Restart the Simple LSP server",
  })

  -- :SimpleLspLog - show LSP log
  vim.api.nvim_create_user_command("SimpleLspLog", function()
    require("simple.lsp").show_log()
  end, {
    desc = "Show the LSP log file",
  })

  -- :SimpleMathToggle - toggle math rendering
  vim.api.nvim_create_user_command("SimpleMathToggle", function()
    require("simple.math").toggle()
  end, {
    desc = "Toggle math block rendering",
  })

  -- :SimpleBuild [args] - run build
  vim.api.nvim_create_user_command("SimpleBuild", function(cmd_opts)
    M.run_build(cmd_opts.args)
  end, {
    nargs = "*",
    desc = "Run Simple build command",
  })

  -- :SimpleLint - run linter
  vim.api.nvim_create_user_command("SimpleLint", function()
    M.run_build("lint")
  end, {
    desc = "Run Simple linter",
  })

  -- :SimpleFormat - run formatter
  vim.api.nvim_create_user_command("SimpleFormat", function()
    M.run_build("fmt")
  end, {
    desc = "Run Simple formatter",
  })

  -- :SimpleTestAtCursor - run test/sdoctest at cursor
  vim.api.nvim_create_user_command("SimpleTestAtCursor", function()
    require("simple.test_lens").run_at_cursor()
  end, {
    desc = "Run test or sdoctest at cursor position",
  })

  -- :SimpleSdoctest [file] - run sdoctest
  vim.api.nvim_create_user_command("SimpleSdoctest", function(cmd_opts)
    if cmd_opts.args and cmd_opts.args ~= "" then
      local cmd_str = table.concat(M._config.commands.test_cmd, " ") .. " --sdoctest " .. cmd_opts.args
      vim.cmd("botright split | terminal " .. cmd_str)
      vim.cmd("startinsert")
    else
      require("simple.test_lens").run_sdoctest()
    end
  end, {
    nargs = "?",
    complete = "file",
    desc = "Run Simple sdoctests (current file or specified path)",
  })

  -- :SimpleTestLensToggle - toggle test lens indicators
  vim.api.nvim_create_user_command("SimpleTestLensToggle", function()
    require("simple.test_lens").toggle()
  end, {
    desc = "Toggle test lens Run indicators",
  })

  -- :SimpleInfo - show plugin info
  vim.api.nvim_create_user_command("SimpleInfo", function()
    M.show_info()
  end, {
    desc = "Show simple.nvim plugin information",
  })

  vim.api.nvim_create_user_command("SimpleTestWorkspace", function()
    require("simple.test_workspace").open()
  end, {
    desc = "Open the Simple test workspace",
  })

  vim.api.nvim_create_user_command("SimpleBreakpointToggle", function()
    require("simple.markers").toggle_breakpoint()
  end, {
    desc = "Toggle a Simple breakpoint sign",
  })

  vim.api.nvim_create_user_command("SimpleBookmarkToggle", function()
    require("simple.markers").toggle_bookmark()
  end, {
    desc = "Toggle a Simple bookmark sign",
  })

  vim.api.nvim_create_user_command("SimplePointerToggle", function()
    require("simple.markers").toggle_pointer()
  end, {
    desc = "Toggle a Simple execution pointer sign",
  })

  vim.api.nvim_create_user_command("SimplePointerClear", function()
    require("simple.markers").clear_pointer()
  end, {
    desc = "Clear the Simple execution pointer sign",
  })

  vim.api.nvim_create_user_command("SimpleBookmarkNext", function()
    require("simple.markers").next_bookmark()
  end, {
    desc = "Jump to the next Simple bookmark",
  })

  vim.api.nvim_create_user_command("SimpleBookmarkPrev", function()
    require("simple.markers").prev_bookmark()
  end, {
    desc = "Jump to the previous Simple bookmark",
  })

  -- Setup keymaps if enabled
  if cfg.keymaps.enabled then
    M._setup_keymaps(cfg.keymaps)
  end
end

--- Run Simple tests
---@param file? string Optional file path or test pattern
function M.run_test(file)
  local cmd = vim.deepcopy(M._config.commands.test_cmd)

  if file and file ~= "" then
    table.insert(cmd, file)
  else
    -- Default to current file if it is a spec file
    local current = vim.api.nvim_buf_get_name(0)
    if current:match("_spec%.spl$") or current:match("/test/") then
      table.insert(cmd, current)
    end
  end

  local cmd_str = table.concat(cmd, " ")

  -- Use terminal for interactive output
  vim.cmd("botright split | terminal " .. cmd_str)
  vim.cmd("startinsert")
end

--- Run Simple build command
---@param args string Build arguments
function M.run_build(args)
  local root = M._find_root()
  local bin = root .. "/bin/simple"
  if vim.fn.executable(bin) ~= 1 then
    bin = "simple"
  end

  local cmd_str = bin .. " build"
  if args and args ~= "" then
    cmd_str = cmd_str .. " " .. args
  end

  vim.cmd("botright split | terminal " .. cmd_str)
  vim.cmd("startinsert")
end

--- Activate brief view: fold all definitions to show only signatures
--- Prefers LSP foldingRange (via vim.lsp.foldexpr) when available (nvim 0.10+),
--- falling back to heuristic _fold_expr when no LSP client is attached.
function M.brief_view()
  local buf = vim.api.nvim_get_current_buf()

  -- Check if an LSP client that supports foldingRange is attached
  local has_lsp_fold = false
  if vim.lsp and vim.lsp.get_clients then
    local clients = vim.lsp.get_clients({ bufnr = buf })
    for _, client in ipairs(clients) do
      local caps = client.server_capabilities or {}
      if caps.foldingRangeProvider then
        has_lsp_fold = true
        break
      end
    end
  end

  if has_lsp_fold and vim.lsp.foldexpr then
    -- Use LSP-backed fold expression (nvim 0.10+)
    vim.wo.foldmethod = "expr"
    vim.wo.foldexpr = "v:lua.vim.lsp.foldexpr()"
    vim.wo.foldlevel = 0
    vim.wo.foldminlines = 1
    vim.wo.foldtext = "v:lua.require('simple.commands')._fold_text()"
    vim.cmd("normal! zM")
    vim.notify("Simple Brief View: LSP folds active. Use :SimpleBriefExpand to expand.", vim.log.levels.INFO)
  else
    -- Fallback: heuristic fold expression
    vim.wo.foldmethod = "expr"
    vim.wo.foldexpr = "v:lua.require('simple.commands')._fold_expr(v:lnum)"
    vim.wo.foldlevel = 0
    vim.wo.foldminlines = 1
    vim.wo.foldtext = "v:lua.require('simple.commands')._fold_text()"
    vim.cmd("normal! zM")
    vim.notify("Simple Brief View: showing signatures only. Use :SimpleBriefExpand to expand.", vim.log.levels.INFO)
  end
end

--- Fold expression for brief view
---@param lnum integer Line number
---@return string
function M._fold_expr(lnum)
  local line = vim.fn.getline(lnum)
  local trimmed = vim.trim(line)

  -- Skip empty lines and comments
  if trimmed == "" or trimmed:match("^#") then
    return "="
  end

  -- Function definitions
  if trimmed:match("^pub%s+") or trimmed:match("^async%s+") then
    if trimmed:match("fn%s+%w+") or trimmed:match("me%s+%w+") then
      return ">1"
    end
  end
  if trimmed:match("^fn%s+%w+") then
    return ">1"
  end
  if trimmed:match("^static%s+fn%s+%w+") then
    return ">1"
  end
  if trimmed:match("^me%s+%w+") then
    return ">1"
  end

  -- Type definitions
  if trimmed:match("^class%s+%w+") or trimmed:match("^struct%s+%w+") then
    return ">1"
  end
  if trimmed:match("^enum%s+%w+") or trimmed:match("^trait%s+%w+") then
    return ">1"
  end
  if trimmed:match("^impl%s+%w+") then
    return ">1"
  end

  -- Test blocks
  if trimmed:match("^describe%s+") or trimmed:match("^context%s+") or trimmed:match("^it%s+") then
    return ">1"
  end

  -- Indentation-based fold end detection
  local indent = vim.fn.indent(lnum)
  local prev_indent = lnum > 1 and vim.fn.indent(lnum - 1) or 0

  if indent < prev_indent and prev_indent > 0 then
    return "<1"
  end

  return "="
end

--- Custom fold text for brief view
---@return string
function M._fold_text()
  local line = vim.fn.getline(vim.v.foldstart)
  local trimmed = vim.trim(line)

  -- Remove trailing colon
  trimmed = trimmed:gsub(":%s*$", "")

  -- Count lines in fold
  local fold_size = vim.v.foldend - vim.v.foldstart + 1

  -- Preserve indentation
  local indent = string.rep(" ", vim.fn.indent(vim.v.foldstart))

  return indent .. trimmed .. " ... (" .. fold_size .. " lines)"
end

--- Show plugin information
function M.show_info()
  local simple = require("simple")
  local ts = require("simple.treesitter")

  local lines = {
    "simple.nvim v" .. simple.version,
    "",
    "Configuration:",
    "  LSP enabled:        " .. tostring(simple.config.lsp.enabled),
    "  LSP cmd:            " .. table.concat(simple.config.lsp.cmd, " "),
    "  Math enabled:       " .. tostring(simple.config.math.enabled),
    "  Math conceal:       " .. tostring(simple.config.math.conceal),
    "  Tree-sitter parser: " .. (ts.is_parser_available() and "installed" or "not installed"),
    "",
    "Commands:",
    "  :SimpleTest [file]      - Run tests",
    "  :SimpleTestAtCursor     - Run test/sdoctest at cursor",
    "  :SimpleSdoctest [file]  - Run sdoctests",
    "  :SimpleTestLensToggle   - Toggle ▶ Run indicators",
    "  :SimpleBrief            - Brief view (fold all)",
    "  :SimpleBriefExpand      - Expand all folds",
    "  :SimpleLspRestart       - Restart LSP",
    "  :SimpleLspLog           - Show LSP log",
    "  :SimpleMathToggle       - Toggle math rendering",
    "  :SimpleBuild [args]     - Run build",
    "  :SimpleLint             - Run linter",
    "  :SimpleFormat           - Run formatter",
    "  :SimpleTestWorkspace    - Open test result workspace",
    "  :SimpleBreakpointToggle - Toggle breakpoint sign",
    "  :SimpleBookmarkToggle   - Toggle bookmark sign",
    "  :SimplePointerToggle    - Toggle execution pointer sign",
    "  :SimplePointerClear     - Clear execution pointer sign",
    "  :SimpleInfo             - This info panel",
    "",
    "Health: Run :checkhealth simple",
  }

  -- Display in a float
  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)
  vim.bo[buf].bufhidden = "wipe"
  vim.bo[buf].modifiable = false

  local width = 60
  local height = #lines
  local win = vim.api.nvim_open_win(buf, true, {
    relative = "editor",
    row = math.floor((vim.o.lines - height) / 2),
    col = math.floor((vim.o.columns - width) / 2),
    width = width,
    height = height,
    style = "minimal",
    border = "rounded",
    title = " simple.nvim ",
    title_pos = "center",
  })

  -- Close on q or <Esc>
  vim.keymap.set("n", "q", function()
    vim.api.nvim_win_close(win, true)
  end, { buffer = buf, silent = true })
  vim.keymap.set("n", "<Esc>", function()
    vim.api.nvim_win_close(win, true)
  end, { buffer = buf, silent = true })
end

--- Find project root
---@return string
function M._find_root()
  local found = vim.fs.find({ "simple.sdn", ".git" }, {
    path = vim.fn.getcwd(),
    upward = true,
    stop = vim.env.HOME,
  })
  if found and #found > 0 then
    return vim.fs.dirname(found[1])
  end
  return vim.fn.getcwd()
end

--- Setup keymaps for Simple files
---@param cfg SimpleKeymapsConfig
function M._setup_keymaps(cfg)
  local group = vim.api.nvim_create_augroup("simple_keymaps", { clear = true })

  vim.api.nvim_create_autocmd("FileType", {
    group = group,
    pattern = "simple",
    callback = function(ev)
      local bufnr = ev.buf
      local p = cfg.prefix
      local opts = { buffer = bufnr, silent = true }

      vim.keymap.set("n", p .. "t", "<cmd>SimpleTest<cr>", vim.tbl_extend("force", opts, { desc = "Run test file" }))
      vim.keymap.set("n", p .. "T", "<cmd>SimpleTestAtCursor<cr>", vim.tbl_extend("force", opts, { desc = "Run test at cursor" }))
      vim.keymap.set("n", p .. "d", "<cmd>SimpleSdoctest<cr>", vim.tbl_extend("force", opts, { desc = "Run sdoctest" }))
      vim.keymap.set("n", p .. "b", "<cmd>SimpleBrief<cr>", vim.tbl_extend("force", opts, { desc = "Brief view" }))
      vim.keymap.set("n", p .. "e", "<cmd>SimpleBriefExpand<cr>", vim.tbl_extend("force", opts, { desc = "Expand all" }))
      vim.keymap.set("n", p .. "m", "<cmd>SimpleMathToggle<cr>", vim.tbl_extend("force", opts, { desc = "Toggle math" }))
      vim.keymap.set("n", p .. "r", "<cmd>SimpleLspRestart<cr>", vim.tbl_extend("force", opts, { desc = "Restart LSP" }))
      vim.keymap.set("n", p .. "i", "<cmd>SimpleInfo<cr>", vim.tbl_extend("force", opts, { desc = "Plugin info" }))
      vim.keymap.set("n", p .. "l", "<cmd>SimpleLint<cr>", vim.tbl_extend("force", opts, { desc = "Lint" }))
      vim.keymap.set("n", p .. "f", "<cmd>SimpleFormat<cr>", vim.tbl_extend("force", opts, { desc = "Format" }))
      vim.keymap.set("n", p .. "w", "<cmd>SimpleTestWorkspace<cr>", vim.tbl_extend("force", opts, { desc = "Test workspace" }))
      vim.keymap.set("n", p .. "x", "<cmd>SimpleBreakpointToggle<cr>", vim.tbl_extend("force", opts, { desc = "Toggle breakpoint" }))
      vim.keymap.set("n", p .. "k", "<cmd>SimpleBookmarkToggle<cr>", vim.tbl_extend("force", opts, { desc = "Toggle bookmark" }))
      vim.keymap.set("n", p .. "p", "<cmd>SimplePointerToggle<cr>", vim.tbl_extend("force", opts, { desc = "Toggle execution pointer" }))
      vim.keymap.set("n", p .. "]", "<cmd>SimpleBookmarkNext<cr>", vim.tbl_extend("force", opts, { desc = "Next bookmark" }))
      vim.keymap.set("n", p .. "[", "<cmd>SimpleBookmarkPrev<cr>", vim.tbl_extend("force", opts, { desc = "Previous bookmark" }))
    end,
  })
end

return M
