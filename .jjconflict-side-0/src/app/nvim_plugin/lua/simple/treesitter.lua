-- lua/simple/treesitter.lua
-- Tree-sitter parser registration and query path management
--
-- The Simple project includes 6 tree-sitter query files at:
--   src/compiler/parser/treesitter/queries/
--
-- Query files:
--   highlights.scm   (538 lines) - Syntax highlighting: 100+ keywords, 50+ scope types
--   locals.scm       (411 lines) - Scope tracking and variable resolution
--   folds.scm        (404 lines) - Code folding regions
--   textobjects.scm  (587 lines) - Semantic text objects for selection/navigation
--   injections.scm   (373 lines) - Embedded language support (15+ injected languages)
--   indents.scm      (454 lines) - Auto-indentation rules

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
--- Looks for queries at src/compiler/parser/treesitter/queries/ in the project tree.
---@param cfg SimpleTreesitterConfig
function M._setup_query_paths(cfg)
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
--- Expected path: src/compiler/parser/treesitter/queries/
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

  return nil
end

--- Register query files from a directory path
---@param query_dir string Path to directory containing .scm files
function M._register_queries(query_dir)
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
        -- Use pcall because the parser might not be installed yet
        pcall(vim.treesitter.query.set, "simple", qt.name, query_text)
      end
    end
  end
end

--- Check if the Simple tree-sitter parser is available
---@return boolean
function M.is_parser_available()
  local ok = pcall(vim.treesitter.language.inspect, "simple")
  return ok
end

--- Get the path to the project's query directory
---@return string|nil
function M.get_query_path()
  return M._find_project_queries()
end

return M
