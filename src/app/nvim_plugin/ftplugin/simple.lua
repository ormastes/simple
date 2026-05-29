-- ftplugin/simple.lua
-- Filetype settings for Simple language buffers

if vim.b.did_ftplugin_simple then
  return
end
vim.b.did_ftplugin_simple = true

-- Indentation
vim.bo.shiftwidth = 4
vim.bo.tabstop = 4
vim.bo.softtabstop = 4
vim.bo.expandtab = true

-- Comments: Simple uses # for line comments
vim.bo.commentstring = "# %s"
vim.bo.comments = ":#"

-- Folding: prefer tree-sitter if available, fall back to indent
if pcall(vim.treesitter.get_parser, 0, "simple") then
  vim.wo.foldmethod = "expr"
  vim.wo.foldexpr = "v:lua.vim.treesitter.foldexpr()"
else
  vim.wo.foldmethod = "indent"
end
vim.wo.foldlevel = 99 -- start with all folds open

-- Keyword characters: allow ? and ! in identifiers for optional/mutable patterns
vim.bo.iskeyword = vim.bo.iskeyword .. ",?,!"

-- File format
vim.bo.fileformat = "unix"

-- Suffix for :find and gf
vim.opt_local.suffixesadd:append(".spl")
vim.opt_local.path:append("src/app,src/core,src/lib")

-- Match pairs for % navigation
vim.opt_local.matchpairs:append("<:>")

-- Undo ftplugin settings on filetype change
vim.b.undo_ftplugin = table.concat({
  "setlocal shiftwidth< tabstop< softtabstop< expandtab<",
  "setlocal commentstring< comments<",
  "setlocal foldmethod< foldexpr< foldlevel<",
  "setlocal iskeyword< fileformat<",
  "setlocal suffixesadd< path< matchpairs<",
}, " | ")
