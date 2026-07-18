<!-- codex-research -->
# Neovim Plugin Worktree Automation - Local Research

## Scope

Audit and harden `src/app/nvim_plugin` so it can be tested directly from the
current repository worktree without requiring a user-installed plugin checkout.

## Findings

- The repo had protocol-level LSP smoke coverage in
  `scripts/simple_lsp_protocol_smoke.py`, but no dedicated headless Neovim
  smoke test for `src/app/nvim_plugin`.
- The plugin is loaded from a worktree runtimepath, so tests must prepend
  `src/app/nvim_plugin` and execute `runtime plugin/simple.lua`.
- LSP command discovery should prefer the worktree `bin/simple lsp`; relying on
  a globally installed `simple` can test a different binary than the checkout.
- Tree-sitter query discovery should work when the editor cwd is the repository
  and when the plugin is loaded from this repository path.
- Command helpers previously built `:terminal` commands by raw string
  concatenation. Tests should cover argv shell escaping.

## Implemented Test Target

- `scripts/smoke/nvim_plugin_smoke.spl` runs isolated `nvim --headless` cases with
  temporary XDG directories and the worktree plugin on runtimepath.
- Covered paths: Lua syntax loading, filetype setup, command registration, LSP
  command validation, Tree-sitter query discovery, ftplugin keyword policy,
  terminal command escaping, and starting the Simple LSP client from the
  worktree command.
