-- lua/simple/math.lua
-- Math block detection, concealment, and extmark rendering for m{ ... } syntax
--
-- NOTE: The LSP hover handler (src/app/lsp/handlers/hover.spl) already provides
-- full math rendering in hover popups via src/lib/math_repr.spl, including:
--   - LaTeX ($$...$$ display math)
--   - Unicode pretty text (to_pretty)
--
-- This module provides ADDITIONAL inline visual feedback by concealing the
-- m{ } delimiters and showing a quick Unicode preview as virtual text.
-- Full rendering is done by the LSP server in hover. This provides quick inline preview.

local M = {}

---@type SimpleMathConfig
M._config = nil

--- Namespace for all math-related extmarks
M._ns = vim.api.nvim_create_namespace("simple_math")

--- Debounce timer handle
M._timer = nil

--- Whether math rendering is currently enabled
M._enabled = false

--- Parsed math block info
---@class MathBlock
---@field start_row integer 0-indexed
---@field start_col integer 0-indexed
---@field end_row integer 0-indexed
---@field end_col integer 0-indexed (exclusive)
---@field content string The expression inside m{ ... }

--- Setup math block detection and concealment
---@param cfg SimpleMathConfig
function M.setup(cfg)
  M._config = cfg
  M._enabled = cfg.enabled

  local group = vim.api.nvim_create_augroup("simple_math", { clear = true })

  -- Scan buffer on enter and after changes
  vim.api.nvim_create_autocmd({ "BufEnter", "BufWinEnter" }, {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if M._enabled then
        M.update_math_blocks(ev.buf)
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

  -- Anti-conceal: reveal math block content on cursor line
  vim.api.nvim_create_autocmd("CursorMoved", {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if M._enabled and M._config.conceal then
        M._on_cursor_moved(ev.buf)
      end
    end,
  })

  -- Auto-show float on CursorHold when inside math block
  vim.api.nvim_create_autocmd("CursorHold", {
    group = group,
    pattern = "*.spl",
    callback = function(ev)
      if M._enabled and M._config.float_on_hover then
        M._on_cursor_hold(ev.buf)
      end
    end,
  })
end

--- Scan buffer for m{ ... } blocks using regex (tree-sitter fallback)
---@param bufnr integer
---@return MathBlock[]
function M.find_math_blocks(bufnr)
  local blocks = {}
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)

  -- State machine to handle multi-line m{ ... } blocks
  local in_block = false
  local brace_depth = 0
  local block_start_row = 0
  local block_start_col = 0
  local content_parts = {}

  for row, line in ipairs(lines) do
    local col = 1

    while col <= #line do
      if not in_block then
        -- Look for m{ pattern (m followed by {, possibly with whitespace)
        local m_start, m_end = line:find("m%s*{", col)
        if m_start then
          in_block = true
          brace_depth = 1
          block_start_row = row - 1 -- convert to 0-indexed
          block_start_col = m_start - 1 -- convert to 0-indexed
          content_parts = {}
          -- Capture content after the opening brace
          local after_brace = line:sub(m_end + 1)
          -- Check for closing brace in the same segment
          local rest_col = m_end + 1
          col = m_end + 1
          local found_close = false
          while col <= #line do
            local ch = line:sub(col, col)
            if ch == "{" then
              brace_depth = brace_depth + 1
            elseif ch == "}" then
              brace_depth = brace_depth - 1
              if brace_depth == 0 then
                -- End of block
                local content = line:sub(rest_col, col - 1)
                table.insert(content_parts, content)
                table.insert(blocks, {
                  start_row = block_start_row,
                  start_col = block_start_col,
                  end_row = row - 1,
                  end_col = col, -- 0-indexed exclusive
                  content = vim.trim(table.concat(content_parts, "\n")),
                })
                in_block = false
                found_close = true
                col = col + 1
                break
              end
            end
            col = col + 1
          end
          if not found_close and in_block then
            -- Content continues on next line
            table.insert(content_parts, line:sub(rest_col))
            col = #line + 1
          end
        else
          col = #line + 1
        end
      else
        -- Inside a math block, scanning for closing brace
        local line_start = col
        while col <= #line do
          local ch = line:sub(col, col)
          if ch == "{" then
            brace_depth = brace_depth + 1
          elseif ch == "}" then
            brace_depth = brace_depth - 1
            if brace_depth == 0 then
              local content = line:sub(line_start, col - 1)
              table.insert(content_parts, content)
              table.insert(blocks, {
                start_row = block_start_row,
                start_col = block_start_col,
                end_row = row - 1,
                end_col = col,
                content = vim.trim(table.concat(content_parts, "\n")),
              })
              in_block = false
              col = col + 1
              break
            end
          end
          col = col + 1
        end
        if in_block then
          table.insert(content_parts, line:sub(line_start))
          col = #line + 1
        end
      end
    end
  end

  return blocks
end

--- Local Unicode rendering for inline preview of math expressions.
--- This mirrors what to_pretty() does in src/lib/math_repr.spl, which delegates
--- to src/lib/unicode_math.spl for Greek letters, superscripts, subscripts,
--- and math symbols. This is a lightweight Lua subset for virtual text display.
---
--- Supported conversions:
---   Superscripts: ^2 -> ², ^3 -> ³, ^n -> ⁿ, ^0..^9
---   Greek:        alpha -> α, beta -> β, gamma -> γ, delta -> δ, pi -> π,
---                 theta -> θ, sigma -> σ, omega -> ω, lambda -> λ, mu -> μ, etc.
---   Math symbols: sqrt -> √, sum -> ∑, integral -> ∫, infinity -> ∞,
---                 partial -> ∂, nabla -> ∇, forall -> ∀, exists -> ∃
---   Operators:    times -> ×, cdot -> ·, pm -> ±, leq -> ≤, geq -> ≥,
---                 neq -> ≠, approx -> ≈, implies -> ⇒, to -> →
local function to_pretty_lua(content)
  local s = content

  -- Superscript map (matches src/lib/unicode_math.spl superscript_char)
  local sup = {
    ["0"] = "⁰", ["1"] = "¹", ["2"] = "²", ["3"] = "³", ["4"] = "⁴",
    ["5"] = "⁵", ["6"] = "⁶", ["7"] = "⁷", ["8"] = "⁸", ["9"] = "⁹",
    ["n"] = "ⁿ", ["i"] = "ⁱ", ["x"] = "ˣ",
    ["+"] = "⁺", ["-"] = "⁻", ["("] = "⁽", [")"] = "⁾",
  }

  -- Replace ^{...} groups and ^X single characters with superscripts
  s = s:gsub("%^{([^}]+)}", function(inner)
    return inner:gsub(".", function(ch) return sup[ch] or ch end)
  end)
  s = s:gsub("%^([%w%+%-])", function(ch) return sup[ch] or ("^" .. ch) end)

  -- Greek letters (matches src/lib/unicode_math.spl greek/greek_upper)
  local greeks = {
    alpha = "α", beta = "β", gamma = "γ", delta = "δ", epsilon = "ε",
    zeta = "ζ", eta = "η", theta = "θ", iota = "ι", kappa = "κ",
    lambda = "λ", mu = "μ", nu = "ν", xi = "ξ", pi = "π",
    rho = "ρ", sigma = "σ", tau = "τ", phi = "φ", chi = "χ",
    psi = "ψ", omega = "ω", partial = "∂", nabla = "∇",
    Gamma = "Γ", Delta = "Δ", Theta = "Θ", Lambda = "Λ", Xi = "Ξ",
    Pi = "Π", Sigma = "Σ", Phi = "Φ", Psi = "Ψ", Omega = "Ω",
  }
  for name, sym in pairs(greeks) do
    s = s:gsub("%f[%a]" .. name .. "%f[^%a]", sym)
  end

  -- Math symbols (matches src/lib/unicode_math.spl math_sym)
  local syms = {
    sqrt = "√", sum = "∑", product = "∏", integral = "∫",
    infinity = "∞", forall = "∀", exists = "∃",
    emptyset = "∅", degree = "°",
  }
  for name, sym in pairs(syms) do
    s = s:gsub("%f[%a]" .. name .. "%f[^%a]", sym)
  end

  -- Operator symbols (matches src/lib/unicode_math.spl math_op)
  local ops = {
    times = "×", cdot = "·", pm = "±",
    leq = "≤", geq = "≥", neq = "≠", approx = "≈", equiv = "≡",
    implies = "⇒", iff = "⇔", to = "→",
  }
  for name, sym in pairs(ops) do
    s = s:gsub("%f[%a]" .. name .. "%f[^%a]", sym)
  end

  return s
end

--- Apply concealment extmarks to detected math blocks
---@param bufnr integer
---@param blocks MathBlock[]
function M.apply_conceal(bufnr, blocks)
  M.clear_conceal(bufnr)

  if not M._config.conceal then
    return
  end

  for _, block in ipairs(blocks) do
    -- Highlight the entire math block region
    if block.start_row == block.end_row then
      -- Single-line math block: conceal m{ and } delimiters
      -- Mark the opening "m{" with conceal
      local open_len = 2 -- "m{"
      -- Check for whitespace between m and {
      local line = vim.api.nvim_buf_get_lines(bufnr, block.start_row, block.start_row + 1, false)[1]
      if line then
        local segment = line:sub(block.start_col + 1, block.start_col + 10)
        local ws = segment:match("^m(%s*){")
        if ws then
          open_len = 2 + #ws
        end
      end

      -- Conceal opening delimiter "m{" or "m {"
      pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, block.start_col, {
        end_col = block.start_col + open_len,
        conceal = "",
        hl_group = "SimpleMathDelimiter",
      })

      -- Highlight the math content
      pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, block.start_col + open_len, {
        end_col = block.end_col - 1,
        hl_group = M._config.highlight_group,
      })

      -- Conceal closing delimiter "}"
      pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, block.end_col - 1, {
        end_col = block.end_col,
        conceal = "",
        hl_group = "SimpleMathDelimiter",
      })

      -- Show inline Unicode preview as virtual text at end of line.
      -- This is a quick visual hint; full rendering (LaTeX + pretty) is
      -- provided by the LSP hover handler (src/app/lsp/handlers/hover.spl)
      -- which calls to_pretty() and render_latex_raw() from src/lib/math_repr.spl.
      local pretty = to_pretty_lua(block.content)
      if pretty ~= block.content then
        pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, 0, {
          virt_text = { { "  " .. pretty, "SimpleMathPretty" } },
          virt_text_pos = "eol",
        })
      end
    else
      -- Multi-line math block: highlight the entire region
      pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, block.start_col, {
        end_row = block.end_row,
        end_col = block.end_col,
        hl_group = M._config.highlight_group,
      })
    end
  end
end

--- Clear all math concealment extmarks from a buffer
---@param bufnr integer
function M.clear_conceal(bufnr)
  vim.api.nvim_buf_clear_namespace(bufnr, M._ns, 0, -1)
end

--- Update math blocks for the given buffer
---@param bufnr integer
function M.update_math_blocks(bufnr)
  if not vim.api.nvim_buf_is_valid(bufnr) then
    return
  end
  local blocks = M.find_math_blocks(bufnr)
  M.apply_conceal(bufnr, blocks)
end

--- Debounced update to avoid excessive recomputation
---@param bufnr integer
function M._debounced_update(bufnr)
  if M._timer then
    M._timer:stop()
  end
  M._timer = vim.defer_fn(function()
    M.update_math_blocks(bufnr)
  end, M._config.update_delay)
end

--- Anti-conceal handler: temporarily reveal content on cursor line
---@param bufnr integer
function M._on_cursor_moved(bufnr)
  local cursor_row = vim.api.nvim_win_get_cursor(0)[1] - 1 -- 0-indexed

  -- Get all extmarks in the buffer
  local marks = vim.api.nvim_buf_get_extmarks(bufnr, M._ns, 0, -1, { details = true })

  for _, mark in ipairs(marks) do
    local mark_row = mark[2]
    local details = mark[4]

    if details and details.conceal then
      local end_row = details.end_row or mark_row
      -- If cursor is on a row that intersects this mark, remove conceal temporarily
      if cursor_row >= mark_row and cursor_row <= end_row then
        -- The cursor is on the math block line -- Neovim's built-in
        -- conceallevel/concealcursor handles per-line anti-conceal.
        -- We set concealcursor appropriately.
        vim.wo.concealcursor = "" -- reveal on current line in normal mode
      end
    end
  end
end

--- CursorHold handler: show float for math block under cursor
---@param bufnr integer
function M._on_cursor_hold(bufnr)
  local pos = vim.api.nvim_win_get_cursor(0)
  local cursor_row = pos[1] - 1
  local cursor_col = pos[2]

  local blocks = M.find_math_blocks(bufnr)
  for _, block in ipairs(blocks) do
    if M._cursor_in_block(cursor_row, cursor_col, block) then
      require("simple.float").show(bufnr, block)
      return
    end
  end
end

--- Check if cursor position is inside a math block
---@param row integer 0-indexed
---@param col integer 0-indexed
---@param block MathBlock
---@return boolean
function M._cursor_in_block(row, col, block)
  if row < block.start_row or row > block.end_row then
    return false
  end
  if row == block.start_row and col < block.start_col then
    return false
  end
  if row == block.end_row and col >= block.end_col then
    return false
  end
  return true
end

--- Toggle math rendering on/off
function M.toggle()
  M._enabled = not M._enabled
  if M._enabled then
    -- Re-render all simple buffers
    for _, bufnr in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(bufnr) and vim.bo[bufnr].filetype == "simple" then
        M.update_math_blocks(bufnr)
      end
    end
    vim.notify("Simple math rendering: ON", vim.log.levels.INFO)
  else
    -- Clear all simple buffers
    for _, bufnr in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(bufnr) then
        M.clear_conceal(bufnr)
      end
    end
    vim.notify("Simple math rendering: OFF", vim.log.levels.INFO)
  end
end

return M
