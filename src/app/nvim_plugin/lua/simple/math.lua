-- lua/simple/math.lua
-- Math-mode block detection, concealment, and extmark rendering for
-- m{}, loss{}, and nograd{} syntax.
--
-- NOTE: The LSP hover handler (src/app/lsp/handlers/hover.spl) already provides
-- full math rendering in hover popups via src/lib/math_repr.spl, including:
--   - LaTeX ($$...$$ display math)
--   - Unicode pretty text (to_pretty)
--
-- This module provides ADDITIONAL inline visual feedback by concealing the
-- block delimiters and showing a quick Unicode preview as virtual text.
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

--- Block type indicators shown when delimiters are concealed
local BLOCK_INDICATORS = {
  math = "∂",     -- partial derivative
  loss = "ℒ",     -- Lagrangian/Loss
  nograd = "∅",   -- no-gradient
}

--- Parsed math-mode block info
---@class MathBlock
---@field block_type string "math"|"loss"|"nograd"
---@field prefix_len integer Length of prefix + `{` (e.g. 2 for m{, 5 for loss{, 7 for nograd{)
---@field start_row integer 0-indexed
---@field start_col integer 0-indexed
---@field end_row integer 0-indexed
---@field end_col integer 0-indexed (exclusive)
---@field content string The expression inside the block

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

--- Block prefix patterns: keyword -> (block_type, prefix_len including `{`)
--- Block prefix patterns ordered longest-first to avoid false matches.
--- Each entry uses %f[%a] (frontier pattern) before the keyword to ensure
--- it only matches at word boundaries (prevents "sum{" matching as "m{").
local BLOCK_PREFIXES = {
  { pattern = "%f[%a]nograd%s*{", block_type = "nograd", base_len = 7 },
  { pattern = "%f[%a]loss%s*{",   block_type = "loss",   base_len = 5 },
  { pattern = "%f[%a]m%s*{",      block_type = "math",   base_len = 2 },
}

--- Scan buffer for math-mode blocks (m{}, loss{}, nograd{}) using regex
---@param bufnr integer
---@return MathBlock[]
function M.find_math_blocks(bufnr)
  local blocks = {}
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)

  -- State machine to handle multi-line blocks
  local in_block = false
  local brace_depth = 0
  local block_start_row = 0
  local block_start_col = 0
  local cur_block_type = "math"
  local cur_prefix_len = 2
  local content_parts = {}

  for row, line in ipairs(lines) do
    local col = 1

    while col <= #line do
      if not in_block then
        -- Try each block prefix pattern, longest first to avoid false matches
        local best_start, best_end, best_type, best_plen = nil, nil, nil, nil
        for _, bp in ipairs(BLOCK_PREFIXES) do
          local s, e = line:find(bp.pattern, col)
          if s and (not best_start or s < best_start) then
            -- Calculate actual prefix length (accounts for whitespace between keyword and {)
            local actual_plen = e - s + 1
            best_start, best_end, best_type, best_plen = s, e, bp.block_type, actual_plen
          end
        end

        if best_start then
          in_block = true
          brace_depth = 1
          block_start_row = row - 1 -- convert to 0-indexed
          block_start_col = best_start - 1 -- convert to 0-indexed
          cur_block_type = best_type
          cur_prefix_len = best_plen
          content_parts = {}
          -- Check for closing brace in the same segment
          local rest_col = best_end + 1
          col = best_end + 1
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
                  block_type = cur_block_type,
                  prefix_len = cur_prefix_len,
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
                block_type = cur_block_type,
                prefix_len = cur_prefix_len,
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
--- Find the matching closing delimiter for a balanced group.
--- Returns (inner, rest) where `inner` is the content between delimiters
--- and `rest` is everything after the closing delimiter.
--- @param s string input starting AFTER the opening delimiter
--- @param open string opening character (e.g. "(", "{", "[")
--- @param close string closing character (e.g. ")", "}", "]")
--- @return string|nil inner content, or nil if unbalanced
--- @return string rest remaining string after close
local function match_balanced(s, open, close)
  local depth = 1
  for i = 1, #s do
    local ch = s:sub(i, i)
    if ch == open then
      depth = depth + 1
    elseif ch == close then
      depth = depth - 1
      if depth == 0 then
        return s:sub(1, i - 1), s:sub(i + 1)
      end
    end
  end
  return nil, s
end

--- Split a balanced argument list on top-level commas.
--- e.g. "1 + 2, frac(3, 4)" → {"1 + 2", "frac(3, 4)"}
--- @param s string
--- @return string[]
local function split_args(s)
  local args = {}
  local depth_p, depth_b, depth_c = 0, 0, 0
  local start = 1
  for i = 1, #s do
    local ch = s:sub(i, i)
    if ch == "(" then depth_p = depth_p + 1
    elseif ch == ")" then depth_p = depth_p - 1
    elseif ch == "[" then depth_b = depth_b + 1
    elseif ch == "]" then depth_b = depth_b - 1
    elseif ch == "{" then depth_c = depth_c + 1
    elseif ch == "}" then depth_c = depth_c - 1
    elseif ch == "," and depth_p == 0 and depth_b == 0 and depth_c == 0 then
      table.insert(args, vim.trim(s:sub(start, i - 1)))
      start = i + 1
    end
  end
  table.insert(args, vim.trim(s:sub(start)))
  return args
end

local function to_pretty_lua(content)
  local s = content

  -- Superscript map (matches src/lib/unicode_math.spl superscript_char)
  local sup = {
    ["0"] = "⁰", ["1"] = "¹", ["2"] = "²", ["3"] = "³", ["4"] = "⁴",
    ["5"] = "⁵", ["6"] = "⁶", ["7"] = "⁷", ["8"] = "⁸", ["9"] = "⁹",
    ["n"] = "ⁿ", ["i"] = "ⁱ", ["x"] = "ˣ",
    ["+"] = "⁺", ["-"] = "⁻", ["("] = "⁽", [")"] = "⁾",
  }

  -- ── Structured function rewriting (before flat substitutions) ──

  -- frac(numer, denom) → (numer)/(denom)
  -- Handles nested calls via balanced matching
  local max_iter = 20
  for _ = 1, max_iter do
    local pos = s:find("%f[%a]frac%s*%(")
    if not pos then break end
    local after_open = s:sub(s:find("%(", pos) + 1)
    local inner, rest = match_balanced(after_open, "(", ")")
    if inner then
      local parts = split_args(inner)
      if #parts >= 2 then
        local numer = to_pretty_lua(vim.trim(parts[1]))
        local denom = to_pretty_lua(vim.trim(parts[2]))
        s = s:sub(1, pos - 1) .. "(" .. numer .. ")/(" .. denom .. ")" .. rest
      else
        break
      end
    else
      break
    end
  end

  -- \frac{numer}{denom} → (numer)/(denom)  (LaTeX style)
  for _ = 1, max_iter do
    local pos = s:find("\\frac%s*{")
    if not pos then break end
    local after_open = s:sub(s:find("{", pos) + 1)
    local numer, rest1 = match_balanced(after_open, "{", "}")
    if numer and rest1 then
      -- expect another {
      local brace = rest1:find("{")
      if brace then
        local after_open2 = rest1:sub(brace + 1)
        local denom, rest2 = match_balanced(after_open2, "{", "}")
        if denom then
          local pretty_n = to_pretty_lua(vim.trim(numer))
          local pretty_d = to_pretty_lua(vim.trim(denom))
          s = s:sub(1, pos - 1) .. "(" .. pretty_n .. ")/(" .. pretty_d .. ")" .. rest2
        else break end
      else break end
    else break end
  end

  -- sqrt(expr) → √(expr)
  for _ = 1, max_iter do
    local pos = s:find("%f[%a]sqrt%s*%(")
    if not pos then break end
    local paren_pos = s:find("%(", pos)
    local after_open = s:sub(paren_pos + 1)
    local inner, rest = match_balanced(after_open, "(", ")")
    if inner then
      s = s:sub(1, pos - 1) .. "√(" .. to_pretty_lua(vim.trim(inner)) .. ")" .. rest
    else break end
  end

  -- \sqrt{expr} → √(expr)  (LaTeX style)
  for _ = 1, max_iter do
    local pos = s:find("\\sqrt%s*{")
    if not pos then break end
    local brace_pos = s:find("{", pos)
    local after_open = s:sub(brace_pos + 1)
    local inner, rest = match_balanced(after_open, "{", "}")
    if inner then
      s = s:sub(1, pos - 1) .. "√(" .. to_pretty_lua(vim.trim(inner)) .. ")" .. rest
    else break end
  end

  -- sum(var, from..to) body → ∑_{var=from}^{to} body
  s = s:gsub("%f[%a]sum%s*%((.-)%)%s*", function(params)
    local parts = split_args(params)
    if #parts >= 2 then
      local var_name = vim.trim(parts[1])
      local range = vim.trim(parts[2])
      local lo, hi = range:match("(.-)%.%.(.+)")
      if lo and hi then
        return "∑(" .. var_name .. "=" .. lo .. ".." .. hi .. ") "
      end
    end
    return "∑(" .. params .. ") "
  end)

  -- integral / int binder → ∫
  s = s:gsub("%f[%a]int%s*%((.-)%)%s*", function(params)
    local parts = split_args(params)
    if #parts >= 2 then
      local var_name = vim.trim(parts[1])
      local range = vim.trim(parts[2])
      local lo, hi = range:match("(.-)%.%.(.+)")
      if lo and hi then
        return "∫(" .. var_name .. "=" .. lo .. ".." .. hi .. ") "
      end
    end
    return "∫(" .. params .. ") "
  end)

  -- product binder → ∏
  s = s:gsub("%f[%a]product%s*%((.-)%)%s*", function(params)
    local parts = split_args(params)
    if #parts >= 2 then
      local var_name = vim.trim(parts[1])
      local range = vim.trim(parts[2])
      local lo, hi = range:match("(.-)%.%.(.+)")
      if lo and hi then
        return "∏(" .. var_name .. "=" .. lo .. ".." .. hi .. ") "
      end
    end
    return "∏(" .. params .. ") "
  end)

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

  -- Math symbols
  local syms = {
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
    implies = "⇒", iff = "⇔", ["to"] = "→",
  }
  for name, sym in pairs(ops) do
    s = s:gsub("%f[%a]" .. name .. "%f[^%a]", sym)
  end

  -- LaTeX backslash commands remaining after structured rewriting
  s = s:gsub("\\pi%f[^%a]", "π")
  s = s:gsub("\\exp%f[^%a]", "exp")
  s = s:gsub("\\ln%f[^%a]", "ln")
  s = s:gsub("\\log%f[^%a]", "log")
  s = s:gsub("\\sin%f[^%a]", "sin")
  s = s:gsub("\\cos%f[^%a]", "cos")
  s = s:gsub("\\tan%f[^%a]", "tan")
  s = s:gsub("\\infty%f[^%a]", "∞")
  s = s:gsub("\\cdot%f[^%a]", "·")
  s = s:gsub("\\times%f[^%a]", "×")
  s = s:gsub("\\pm%f[^%a]", "±")
  s = s:gsub("\\leq%f[^%a]", "≤")
  s = s:gsub("\\geq%f[^%a]", "≥")
  s = s:gsub("\\neq%f[^%a]", "≠")
  s = s:gsub("\\approx%f[^%a]", "≈")
  s = s:gsub("\\partial%f[^%a]", "∂")
  s = s:gsub("\\nabla%f[^%a]", "∇")
  s = s:gsub("\\forall%f[^%a]", "∀")
  s = s:gsub("\\exists%f[^%a]", "∃")

  -- Transpose: x' → xᵀ
  s = s:gsub("([%w%)%]])%s*'", "%1ᵀ")

  -- Broadcast operators MUST come before scalar * substitution
  -- .+ .- .* ./ .^ → ⊕ ⊖ ⊙ ⊘ ⊛ (element-wise)
  s = s:gsub("%.%+", "⊕")
  s = s:gsub("%.%-", "⊖")
  s = s:gsub("%.%*", "⊙")
  s = s:gsub("%.%/", "⊘")
  s = s:gsub("%.%^", "⊛")

  -- Explicit * → · (multiplication dot)
  s = s:gsub("%s*%*%s*", "·")
  -- Matrix multiply @ → ⊗
  s = s:gsub("%s*@%s*", "⊗")

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
    local open_len = block.prefix_len
    local indicator = BLOCK_INDICATORS[block.block_type] or "∂"

    -- Highlight the block region
    if block.start_row == block.end_row then
      -- Single-line block: conceal delimiters and show rendered preview

      -- Conceal opening delimiter (e.g. "m{", "loss{", "nograd{")
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

      -- Show indicator + inline Unicode preview as virtual text at end of line
      local pretty = to_pretty_lua(block.content)
      if pretty ~= block.content then
        pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, 0, {
          virt_text = { { "  " .. indicator .. " " .. pretty, "SimpleMathPretty" } },
          virt_text_pos = "eol",
        })
      else
        -- Even without conversion, show the block type indicator
        pcall(vim.api.nvim_buf_set_extmark, bufnr, M._ns, block.start_row, 0, {
          virt_text = { { "  " .. indicator, "SimpleMathPretty" } },
          virt_text_pos = "eol",
        })
      end
    else
      -- Multi-line block: highlight the entire region
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
