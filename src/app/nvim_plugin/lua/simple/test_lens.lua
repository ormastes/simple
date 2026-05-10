-- lua/simple/test_lens.lua
-- Test lens: shows "▶ Run" virtual text beside describe/it/context/sdoctest blocks.
-- Provides keymaps to run the test file or sdoctest at cursor.

local M = {}

--- Namespace for test lens extmarks
M._ns = vim.api.nvim_create_namespace("simple_test_lens")

--- Whether test lens is enabled
M._enabled = false

--- Debounce timer
M._timer = nil

--- Config reference
M._config = nil

--- Patterns for test block detection (order: longest match first)
local TEST_PATTERNS = {
  { pattern = "^(%s*)(describe)%s+\"([^\"]+)\":", kind = "describe" },
  { pattern = "^(%s*)(context)%s+\"([^\"]+)\":", kind = "context" },
  { pattern = "^(%s*)(it)%s+\"([^\"]+)\":",      kind = "it" },
}

--- Pattern for sdoctest in docstrings
local SDOCTEST_PATTERN = "^%s*\"\"\"%s*sdoctest:"

--- Setup test lens
---@param cfg table
function M.setup(cfg)
  M._config = cfg
  M._enabled = true

  local group = vim.api.nvim_create_augroup("simple_test_lens", { clear = true })

  -- Scan on buffer enter
  vim.api.nvim_create_autocmd({ "BufEnter", "BufWinEnter" }, {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if M._enabled then
        M.update(ev.buf)
      end
    end,
  })

  -- Debounced update on text change
  vim.api.nvim_create_autocmd({ "TextChanged", "TextChangedI" }, {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if M._enabled then
        M._debounced_update(ev.buf)
      end
    end,
  })
end

--- Detect test blocks in buffer
---@param bufnr integer
---@return table[] List of {kind, label, line (0-indexed)}
function M.find_test_blocks(bufnr)
  local blocks = {}
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)

  for i, line in ipairs(lines) do
    -- Check test patterns
    for _, tp in ipairs(TEST_PATTERNS) do
      local indent, keyword, label = line:match(tp.pattern)
      if indent then
        table.insert(blocks, {
          kind = tp.kind,
          label = label,
          line = i - 1, -- 0-indexed
        })
        break
      end
    end

    -- Check sdoctest
    if line:match(SDOCTEST_PATTERN) then
      table.insert(blocks, {
        kind = "sdoctest",
        label = "sdoctest",
        line = i - 1,
      })
    end
  end

  return blocks
end

--- Apply virtual text indicators to test blocks
---@param bufnr integer
function M.update(bufnr)
  if not vim.api.nvim_buf_is_valid(bufnr) then
    return
  end

  -- Clear old marks
  vim.api.nvim_buf_clear_namespace(bufnr, M._ns, 0, -1)

  if not M._enabled then
    return
  end

  local blocks = M.find_test_blocks(bufnr)

  for _, block in ipairs(blocks) do
    local text, hl
    if block.kind == "describe" then
      text = "▶ Run File"
      hl = "SimpleTestPass"
    elseif block.kind == "sdoctest" then
      text = "▶ Run Doctest"
      hl = "SimpleTestPending"
    else
      text = "▶ Run Test"
      hl = "SimpleTestPass"
    end

    pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.line, 0, {
      virt_text = { { "  " .. text, hl } },
      virt_text_pos = "eol",
    })
  end
end

--- Debounced update
---@param bufnr integer
function M._debounced_update(bufnr)
  if M._timer then
    M._timer:stop()
  end
  M._timer = vim.defer_fn(function()
    M.update(bufnr)
  end, 300)
end

--- Run test file for the current buffer
function M.run_file()
  local file = vim.api.nvim_buf_get_name(0)
  if file == "" then
    vim.notify("No file to test", vim.log.levels.WARN)
    return
  end

  local cmd = M._get_simple_cmd() .. " test \"" .. file .. "\""
  vim.cmd("botright split | terminal " .. cmd)
  vim.cmd("startinsert")
end

--- Run sdoctest for the current buffer
function M.run_sdoctest()
  local file = vim.api.nvim_buf_get_name(0)
  if file == "" then
    vim.notify("No file to test", vim.log.levels.WARN)
    return
  end

  local cmd = M._get_simple_cmd() .. " test --sdoctest \"" .. file .. "\""
  vim.cmd("botright split | terminal " .. cmd)
  vim.cmd("startinsert")
end

--- Run test or sdoctest based on cursor position
function M.run_at_cursor()
  local cursor_row = vim.api.nvim_win_get_cursor(0)[1] - 1 -- 0-indexed
  local bufnr = vim.api.nvim_get_current_buf()
  local blocks = M.find_test_blocks(bufnr)

  -- Find the nearest block at or above cursor
  local nearest = nil
  for _, block in ipairs(blocks) do
    if block.line <= cursor_row then
      nearest = block
    end
  end

  if nearest and nearest.kind == "sdoctest" then
    M.run_sdoctest()
  else
    M.run_file()
  end
end

--- Toggle test lens on/off
function M.toggle()
  M._enabled = not M._enabled
  if M._enabled then
    for _, bufnr in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(bufnr) and vim.bo[bufnr].filetype == "simple" then
        M.update(bufnr)
      end
    end
    vim.notify("Simple test lens: ON", vim.log.levels.INFO)
  else
    for _, bufnr in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(bufnr) then
        vim.api.nvim_buf_clear_namespace(bufnr, M._ns, 0, -1)
      end
    end
    vim.notify("Simple test lens: OFF", vim.log.levels.INFO)
  end
end

--- Get simple binary command
---@return string
function M._get_simple_cmd()
  if M._config and M._config.commands and M._config.commands.test_cmd then
    return table.concat(M._config.commands.test_cmd, " ")
  end
  -- Find project root
  local found = vim.fs.find({ "simple.sdn", ".git" }, {
    path = vim.fn.getcwd(),
    upward = true,
    stop = vim.env.HOME,
  })
  if found and #found > 0 then
    local root = vim.fs.dirname(found[1])
    local bin = root .. "/bin/simple"
    if vim.fn.executable(bin) == 1 then
      return bin
    end
  end
  return "simple"
end

return M
