-- lua/simple/markers.lua
-- Source editor markers for Simple files:
-- - Breakpoints
-- - Bookmarks
-- - Execution pointer

local M = {}

local GROUP = "simple_markers"

M._state = {}

local function sign_defs()
  vim.fn.sign_define("SimpleBreakpoint", {
    text = "●",
    texthl = "DiagnosticError",
    linehl = "",
    numhl = "",
  })
  vim.fn.sign_define("SimpleBookmark", {
    text = "◆",
    texthl = "DiagnosticInfo",
    linehl = "",
    numhl = "",
  })
  vim.fn.sign_define("SimpleExecutionPointer", {
    text = "▶",
    texthl = "DiagnosticWarn",
    linehl = "Visual",
    numhl = "",
  })
end

function M.setup()
  sign_defs()

  local group = vim.api.nvim_create_augroup("simple_markers", { clear = true })
  vim.api.nvim_create_autocmd({ "BufEnter", "BufWinEnter", "TextChanged", "TextChangedI" }, {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if vim.bo[ev.buf].filetype == "simple" then
        M.refresh(ev.buf)
      end
    end,
  })
end

function M.toggle_breakpoint()
  local bufnr = vim.api.nvim_get_current_buf()
  local line = vim.api.nvim_win_get_cursor(0)[1]
  local state = M._get_state(bufnr)
  if state.breakpoints[line] then
    state.breakpoints[line] = nil
  else
    state.breakpoints[line] = true
  end
  M.refresh(bufnr)
end

function M.toggle_bookmark()
  local bufnr = vim.api.nvim_get_current_buf()
  local line = vim.api.nvim_win_get_cursor(0)[1]
  local state = M._get_state(bufnr)
  if state.bookmarks[line] then
    state.bookmarks[line] = nil
  else
    state.bookmarks[line] = true
  end
  M.refresh(bufnr)
end

function M.toggle_pointer()
  local bufnr = vim.api.nvim_get_current_buf()
  local line = vim.api.nvim_win_get_cursor(0)[1]
  local state = M._get_state(bufnr)
  if state.pointer == line then
    state.pointer = nil
  else
    state.pointer = line
  end
  M.refresh(bufnr)
end

function M.clear_pointer()
  local bufnr = vim.api.nvim_get_current_buf()
  M._get_state(bufnr).pointer = nil
  M.refresh(bufnr)
end

function M.next_bookmark()
  M._jump_to_mark(true)
end

function M.prev_bookmark()
  M._jump_to_mark(false)
end

function M.refresh(bufnr)
  if not vim.api.nvim_buf_is_valid(bufnr) then
    return
  end

  vim.fn.sign_unplace(GROUP, { buffer = bufnr })

  local state = M._get_state(bufnr)
  for line, enabled in pairs(state.breakpoints) do
    if enabled then
      vim.fn.sign_place(0, GROUP, "SimpleBreakpoint", bufnr, { lnum = line, priority = 90 })
    end
  end
  for line, enabled in pairs(state.bookmarks) do
    if enabled then
      vim.fn.sign_place(0, GROUP, "SimpleBookmark", bufnr, { lnum = line, priority = 80 })
    end
  end
  if state.pointer then
    vim.fn.sign_place(0, GROUP, "SimpleExecutionPointer", bufnr, { lnum = state.pointer, priority = 100 })
  end
end

function M._get_state(bufnr)
  local state = M._state[bufnr]
  if not state then
    state = { breakpoints = {}, bookmarks = {}, pointer = nil }
    M._state[bufnr] = state
  end
  return state
end

function M._jump_to_mark(forward)
  local bufnr = vim.api.nvim_get_current_buf()
  local state = M._get_state(bufnr)
  local marks = {}
  for line, enabled in pairs(state.bookmarks) do
    if enabled then
      table.insert(marks, line)
    end
  end
  table.sort(marks)
  if #marks == 0 then
    vim.notify("No bookmarks set", vim.log.levels.INFO)
    return
  end

  local current = vim.api.nvim_win_get_cursor(0)[1]
  local target = marks[1]
  if forward then
    for _, line in ipairs(marks) do
      if line > current then
        target = line
        break
      end
    end
  else
    for i = #marks, 1, -1 do
      if marks[i] < current then
        target = marks[i]
        break
      end
    end
  end

  vim.api.nvim_win_set_cursor(0, { target, 0 })
  vim.cmd("normal! zz")
end

return M
