-- ftdetect/simple.lua
-- Filetype detection for Simple language (.spl files)

vim.filetype.add({
  extension = {
    spl = "simple",
  },
  filename = {
    ["simple.sdn"] = "sdn",
  },
})
