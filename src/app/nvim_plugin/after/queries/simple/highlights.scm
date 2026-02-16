;; after/queries/simple/highlights.scm
;; Minimal highlight overrides for Simple language
;; The primary highlight queries are at src/compiler/parser/treesitter/queries/highlights.scm
;; and are loaded by the treesitter.lua module.
;;
;; This file provides fallback highlights for when the project queries
;; are not available or when additional Neovim-specific captures are needed.

;; Map Simple-specific captures to standard Neovim highlight groups

;; Pipe and compose operators get special highlighting
;; ("|>" @operator.pipeline) => @operator
;; (">>" @operator.pipeline) => @operator

;; Math blocks
;; (math_block) @embedded.math => @string.special

;; Pass variants as TODO-like highlights
;; ("pass_todo") @keyword.control => @todo
