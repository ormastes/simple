-- lua/simple/test_workspace.lua
-- Open a scratch buffer showing structured test-runner artifacts.

local M = {}

M._buf = nil
M._entries = {}
M._line_map = {}
M._summary = { total = 0, passed = 0, failed = 0, skipped = 0, latest = "" }

local function artifact_roots()
  local roots = {}
  local cwd = vim.fn.getcwd()
  local candidates = {
    cwd .. "/target/test-artifacts",
    cwd .. "/build/test-artifacts",
  }
  for _, root in ipairs(candidates) do
    if vim.fn.isdirectory(root) == 1 then
      table.insert(roots, root)
    end
  end
  return roots
end

local function scan_result_files(root, out)
  local entries = vim.fn.readdir(root)
  for _, name in ipairs(entries) do
    local full = root .. "/" .. name
    if vim.fn.isdirectory(full) == 1 then
      scan_result_files(full, out)
    elseif name == "result.json" then
      table.insert(out, full)
    end
  end
end

local function read_json(path)
  local lines = vim.fn.readfile(path)
  if not lines or #lines == 0 then
    return nil
  end
  local ok, decoded = pcall(vim.json.decode, table.concat(lines, "\n"))
  if ok then
    return decoded
  end
  return nil
end

function M.collect()
  local results = {}
  local summary = { total = 0, passed = 0, failed = 0, skipped = 0, latest = "" }
  for _, root in ipairs(artifact_roots()) do
    local files = {}
    scan_result_files(root, files)
    for _, result_path in ipairs(files) do
      local json = read_json(result_path)
      if json then
        local stat = vim.loop.fs_stat(result_path)
        local entry = {
          source_path = json.source_path or "",
          artifact_directory = json.artifact_directory or "",
          status = json.status or "pending",
          passed = (json.counts and json.counts.passed) or 0,
          failed = (json.counts and json.counts.failed) or 0,
          skipped = (json.counts and json.counts.skipped) or 0,
          duration_ms = (json.counts and json.counts.duration_ms) or 0,
          result_json = result_path,
          updated_at = (stat and stat.mtime and stat.mtime.sec) or 0,
        }
        table.insert(results, entry)
      end
    end
  end

  table.sort(results, function(a, b)
    return a.updated_at > b.updated_at
  end)
  for idx, entry in ipairs(results) do
    summary.total = summary.total + 1
    summary.passed = summary.passed + entry.passed
    summary.failed = summary.failed + entry.failed
    summary.skipped = summary.skipped + entry.skipped
    if idx == 1 then
      summary.latest = entry.source_path ~= "" and entry.source_path or entry.artifact_directory
    end
  end
  M._summary = summary
  return results
end

function M.open()
  local entries = M.collect()
  M._entries = entries
  M._line_map = {}
  M._buf = vim.api.nvim_create_buf(false, true)
  vim.bo[M._buf].bufhidden = "wipe"
  vim.bo[M._buf].filetype = "simpletestworkspace"
  vim.bo[M._buf].modifiable = true
  vim.bo[M._buf].swapfile = false

  M._render(entries)

  local width = math.min(120, math.max(80, math.floor(vim.o.columns * 0.65)))
  local height = math.min(30, math.max(10, vim.api.nvim_buf_line_count(M._buf) + 2))
  local win = vim.api.nvim_open_win(M._buf, true, {
    relative = "editor",
    row = math.floor((vim.o.lines - height) / 2),
    col = math.floor((vim.o.columns - width) / 2),
    width = width,
    height = height,
    style = "minimal",
    border = "rounded",
    title = " Simple Test Workspace ",
    title_pos = "center",
  })

  vim.keymap.set("n", "q", function()
    if vim.api.nvim_win_is_valid(win) then
      vim.api.nvim_win_close(win, true)
    end
  end, { buffer = M._buf, silent = true })

  vim.keymap.set("n", "r", function()
    M.refresh()
  end, { buffer = M._buf, silent = true })

  vim.keymap.set("n", "<cr>", function()
    M.open_source()
  end, { buffer = M._buf, silent = true })

  vim.keymap.set("n", "R", function()
    M.rerun_current()
  end, { buffer = M._buf, silent = true })

  vim.keymap.set("n", "o", function()
    M.open_artifacts()
  end, { buffer = M._buf, silent = true })

  vim.keymap.set("n", "l", function()
    M.open_latest()
  end, { buffer = M._buf, silent = true })
end

function M.refresh()
  if not M._buf or not vim.api.nvim_buf_is_valid(M._buf) then
    M.open()
    return
  end
  local entries = M.collect()
  M._entries = entries
  M._line_map = {}
  M._render(entries)
end

function M.open_source()
  local entry = M._entry_at_cursor()
  if not entry or entry.source_path == "" then
    vim.notify("No test entry under cursor", vim.log.levels.WARN)
    return
  end
  vim.cmd("edit " .. vim.fn.fnameescape(entry.source_path))
end

function M.open_latest()
  if not M._entries[1] then
    vim.notify("No test entries available", vim.log.levels.INFO)
    return
  end
  local entry = M._entries[1]
  local target = entry.source_path ~= "" and entry.source_path or entry.artifact_directory
  if target == "" then
    vim.notify("Latest entry has no source or artifact path", vim.log.levels.WARN)
    return
  end
  vim.cmd("edit " .. vim.fn.fnameescape(target))
end

function M.open_artifacts()
  local entry = M._entry_at_cursor()
  if not entry or entry.artifact_directory == "" then
    vim.notify("No artifact directory under cursor", vim.log.levels.WARN)
    return
  end
  M._open_path(entry.artifact_directory)
end

function M.rerun_current()
  local entry = M._entry_at_cursor()
  if not entry or entry.source_path == "" then
    vim.notify("No test entry under cursor", vim.log.levels.WARN)
    return
  end
  local cmd = M._simple_cmd() .. ' test "' .. entry.source_path .. '"'
  if entry.source_path:match("%.md$") then
    cmd = M._simple_cmd() .. ' test --sdoctest "' .. entry.source_path .. '"'
  end
  vim.cmd("botright split | terminal " .. cmd)
  vim.cmd("startinsert")
end

function M._open_path(path)
  if vim.ui and vim.ui.open then
    vim.ui.open(path)
    return
  end
  if vim.fn.has("mac") == 1 then
    vim.fn.jobstart({ "open", path }, { detach = true })
    return
  end
  if vim.fn.executable("xdg-open") == 1 then
    vim.fn.jobstart({ "xdg-open", path }, { detach = true })
    return
  end
  vim.notify("No file opener available for: " .. path, vim.log.levels.WARN)
end

function M._simple_cmd()
  local root = vim.fn.getcwd() .. "/bin/simple"
  if vim.fn.executable(root) == 1 then
    return root
  end
  return "simple"
end

function M._entry_at_cursor()
  local row = vim.api.nvim_win_get_cursor(0)[1]
  for idx = #M._line_map, 1, -1 do
    if row >= M._line_map[idx] then
      return M._entries[idx]
    end
  end
  return nil
end

function M._render(entries)
  local summary = M._summary
  local lines = {
    "Simple Test Workspace",
    "",
    string.format("Results: %d  Passed: %d  Failed: %d  Skipped: %d", summary.total, summary.passed, summary.failed, summary.skipped),
    string.format("Latest: %s", summary.latest ~= "" and summary.latest or "none"),
    "",
    "r  refresh",
    "<cr> open source",
    "R  rerun source file",
    "o  open artifact dir",
    "l  open latest source",
    "",
  }

  if #entries == 0 then
    table.insert(lines, "No test artifacts found.")
  else
    for idx, entry in ipairs(entries) do
      local header_line = #lines + 1
      table.insert(lines, string.format("[%s] %s", entry.status, entry.source_path))
      table.insert(lines, string.format("  pass=%d fail=%d skip=%d time=%dms", entry.passed, entry.failed, entry.skipped, entry.duration_ms))
      table.insert(lines, string.format("  artifacts: %s", entry.artifact_directory))
      table.insert(lines, "")
      M._line_map[idx] = header_line
    end
  end

  vim.bo[M._buf].modifiable = true
  vim.api.nvim_buf_set_lines(M._buf, 0, -1, false, lines)
  vim.bo[M._buf].modifiable = false
end

return M
