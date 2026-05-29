-- lua/simple/float.lua
-- Float window for displaying original math block source

local M = {}

--- Window ID of the currently open float (nil if none)
M._win = nil

--- Buffer ID of the float content
M._buf = nil

--- Show a float window displaying the math block source
---@param bufnr integer Source buffer
---@param block MathBlock Math block range and content
function M.show(bufnr, block)
  -- Close any existing float first
  M.close()

  if not block or not block.content or block.content == "" then
    return
  end

  -- Build float content lines
  local content_lines = vim.split(block.content, "\n", { plain = true })

  -- Calculate float dimensions
  local max_width = 0
  for _, line in ipairs(content_lines) do
    max_width = math.max(max_width, vim.fn.strdisplaywidth(line))
  end

  local width = math.min(math.max(max_width + 2, 20), 80)
  local height = math.min(#content_lines, 10)

  -- Create a scratch buffer for float content
  M._buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_lines(M._buf, 0, -1, false, content_lines)
  vim.bo[M._buf].filetype = "simple"
  vim.bo[M._buf].bufhidden = "wipe"
  vim.bo[M._buf].modifiable = false

  -- Position the float near the math block
  local win_row = block.start_row - vim.fn.line("w0") + 1
  local win_col = block.start_col

  -- Open the float window
  M._win = vim.api.nvim_open_win(M._buf, false, {
    relative = "win",
    row = win_row + 1,
    col = win_col,
    width = width,
    height = height,
    style = "minimal",
    border = "rounded",
    title = " m{ } block ",
    title_pos = "center",
    focusable = false,
    noautocmd = true,
  })

  -- Apply highlight groups to the float
  if M._win and vim.api.nvim_win_is_valid(M._win) then
    vim.api.nvim_win_set_option(M._win, "winhl", "Normal:SimpleMathFloat,FloatBorder:SimpleMathFloatBorder")
    vim.api.nvim_win_set_option(M._win, "wrap", false)
  end

  -- Auto-close on cursor movement
  vim.api.nvim_create_autocmd({ "CursorMoved", "CursorMovedI", "BufLeave", "InsertEnter" }, {
    group = vim.api.nvim_create_augroup("simple_math_float_close", { clear = true }),
    callback = function()
      M.close()
      return true -- remove the autocommand
    end,
  })
end

--- Close the math float window if it is open
function M.close()
  if M._win and vim.api.nvim_win_is_valid(M._win) then
    vim.api.nvim_win_close(M._win, true)
  end
  M._win = nil

  if M._buf and vim.api.nvim_buf_is_valid(M._buf) then
    vim.api.nvim_buf_delete(M._buf, { force = true })
  end
  M._buf = nil
end

return M
