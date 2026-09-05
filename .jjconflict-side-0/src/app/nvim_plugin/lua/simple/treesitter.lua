-- lua/simple/treesitter.lua
-- Tree-sitter parser registration and query path management
--
-- The Simple project keeps Neovim-compatible tree-sitter queries at:
--   src/compiler/10.frontend/parser/treesitter/queries/

local M = {}

--- Whether tree-sitter has been configured
M._configured = false

--- Setup tree-sitter for the Simple language
---@param cfg SimpleTreesitterConfig
function M.setup(cfg)
  if M._configured then
    return
  end

  -- Register filetype-to-parser mapping
  if vim.treesitter.language then
    pcall(vim.treesitter.language.register, "simple", "simple")
  end

  -- Register parser configuration for nvim-treesitter if available
  local ok, parsers = pcall(require, "nvim-treesitter.parsers")
  if ok and parsers then
    local parser_config = parsers.get_parser_configs()
    if parser_config and not parser_config.simple then
      parser_config.simple = {
        install_info = {
          -- Tree-sitter grammar source for Simple
          -- Users should point this to their local or remote grammar
          url = "https://github.com/nicholasgasior/tree-sitter-simple",
          files = { "src/parser.c" },
          branch = "main",
          generate_requires_npm = false,
          requires_generate_from_grammar = false,
        },
        filetype = "simple",
        maintainers = {},
      }
    end
  end

  -- Set up query paths to reference the project's existing queries
  M._setup_query_paths(cfg)

  M._configured = true
end

--- Configure query paths so Neovim finds the existing .scm files
--- Looks for queries in the project tree or relative to this plugin checkout.
---@param cfg SimpleTreesitterConfig
function M._setup_query_paths(cfg)
  cfg = cfg or {}
  local query_path = cfg.query_path

  -- Auto-detect: look for the queries in the project tree
  if not query_path then
    query_path = M._find_project_queries()
  end

  if not query_path then
    return
  end

  -- Register query files with Neovim's tree-sitter
  -- Neovim looks for queries in runtime paths under queries/<lang>/
  -- We create a symlink or add the path so Neovim can find them
  M._register_queries(query_path)
end

--- Find the project's tree-sitter query directory
--- Expected path: src/compiler/10.frontend/parser/treesitter/queries/
---@return string|nil
function M._find_project_queries()
  -- Search upward from cwd for the queries directory
  local markers = {
    "src/compiler/parser/treesitter/queries/highlights.scm",
  }

  local found = vim.fs.find(markers, {
    path = vim.fn.getcwd(),
    upward = true,
    stop = vim.env.HOME,
    type = "file",
  })

  if found and #found > 0 then
    return vim.fs.dirname(found[1])
  end

  -- When the plugin is loaded from this repository, derive the query path from
  -- this module location instead of relying on the editor cwd.
  local source = debug.getinfo(1, "S").source
  if source and vim.startswith(source, "@") then
    local plugin_root = vim.fs.dirname(vim.fs.dirname(vim.fs.dirname(source:sub(2))))
    local repo_root = vim.fs.dirname(vim.fs.dirname(vim.fs.dirname(plugin_root)))
    local repo_queries = repo_root .. "/src/compiler/10.frontend/parser/treesitter/queries"
    if vim.fn.filereadable(repo_queries .. "/highlights.scm") == 1 then
      return repo_queries
    end

    local legacy_queries = repo_root .. "/src/compiler/parser/treesitter/queries"
    if vim.fn.filereadable(legacy_queries .. "/highlights.scm") == 1 then
      return legacy_queries
    end
  end

  return nil
end

--- Register query files from a directory path
---@param query_dir string Path to directory containing .scm files
function M._register_queries(query_dir)
  if type(query_dir) ~= "string" or query_dir == "" or vim.fn.isdirectory(query_dir) ~= 1 then
    return
  end

  if not (vim.treesitter and vim.treesitter.query and vim.treesitter.query.set) then
    return
  end

  -- Read and register each query type
  local query_types = {
    { file = "highlights.scm", name = "highlights" },
    { file = "folds.scm", name = "folds" },
    { file = "indents.scm", name = "indents" },
    { file = "injections.scm", name = "injections" },
    { file = "locals.scm", name = "locals" },
    { file = "textobjects.scm", name = "textobjects" },
  }

  for _, qt in ipairs(query_types) do
    local filepath = query_dir .. "/" .. qt.file
    if vim.fn.filereadable(filepath) == 1 then
      local content = vim.fn.readfile(filepath)
      if content and #content > 0 then
        local query_text = table.concat(content, "\n")
        local ok, err = pcall(vim.treesitter.query.set, "simple", qt.name, query_text)
        if not ok then
          vim.notify(
            string.format("simple.nvim: failed to load %s tree-sitter query: %s", qt.name, tostring(err)),
            vim.log.levels.WARN
          )
        end
      end
    end
  end
end

--- Check if the Simple tree-sitter parser is available
---@return boolean
function M.is_parser_available()
  if not (vim.treesitter and vim.treesitter.language and vim.treesitter.language.inspect) then
    return false
  end
  local ok = pcall(vim.treesitter.language.inspect, "simple")
  return ok
end

--- Get the path to the project's query directory
---@return string|nil
function M.get_query_path()
  return M._find_project_queries()
end

return M
