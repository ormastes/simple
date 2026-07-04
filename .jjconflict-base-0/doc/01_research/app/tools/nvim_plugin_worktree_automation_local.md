<!-- codex-research -->
# Neovim Plugin Worktree Automation - Domain Research

## Sources

- Neovim Lua plugin documentation:
  https://neovim.io/doc/user/lua-plugin/
- Neovim development test documentation:
  https://neovim.io/doc/user/dev_test.html
- Neovim Lua documentation:
  https://neovim.io/doc/user/lua.html

## Relevant Guidance

- Lua plugins are discovered from runtimepath directories. A `plugin/*.lua`
  file is loaded eagerly, while modules under `lua/` should be required lazily.
- Plugin startup code should stay small and defer module loading until commands,
  mappings, or explicit setup calls need it.
- Headless Neovim is suitable for automated integration tests because it can
  execute real runtimepath loading, filetype detection, `ftplugin` behavior,
  Lua APIs, and LSP client startup.
- Neovim's own test documentation treats functional tests as real Nvim process
  tests. For third-party plugin worktree automation, a small headless smoke
  runner is a pragmatic equivalent when the repo does not already carry a
  Busted/plenary/mini.test dependency.
- Lua plugin code should target Neovim's Lua 5.1-compatible runtime and avoid
  depending on non-Neovim Lua behavior when tests run inside `nvim --headless`.

## Applied Approach

- Use an isolated XDG/HOME per test process to avoid user config leakage.
- Prepend the worktree plugin path to runtimepath so the test always exercises
  the current checkout.
- Test the highest-risk integration paths through real Neovim APIs instead of
  stubbing `vim`.
- Keep the harness dependency-free: Python starts Neovim; Neovim executes the
  Lua assertions.
