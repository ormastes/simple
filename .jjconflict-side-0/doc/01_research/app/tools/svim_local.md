# svim Domain Research

## Summary

The supplied plan already fixed the relevant external defaults, so this artifact records the chosen domain conclusions that drive implementation:

- Vim/Neovim-style editor model: separate `Buffer`, `Window`, and `Tabpage`.
- Stable annotation tracking: extmark-like anchors that survive edits.
- Incremental language-service direction: editor consumes existing parser/tree-sitter/LSP infrastructure instead of forking grammar logic.
- Message-based remote control: stable RPC boundary for tooling, tests, and future compatibility layers.

## Domain Defaults Adopted

- Buffer/window/tabpage separation keeps multi-view editing composable and is the right base for host TUI plus future SimpleOS and GUI shells.
- Anchored annotations are mandatory for diagnostics, search hits, future code lenses, and plugin overlays. Raw cursor coordinates alone are too brittle across edits.
- Modal editing remains the user-facing interaction model in v1: `Normal`, `Insert`, `Visual`, `Command`.
- RPC should look like the repo’s existing JSON-RPC/LSP-style tool boundaries rather than importing a Neovim compatibility layer in v1.

## Implications For This Increment

- The first implementation increment should expose editor-native public types even if some deeper subsystems remain simplified.
- The shell boundary should stay thin: render snapshot in the surface, mutate text only through the shared session API.
- The design must leave room for future parser/decorations and SimpleOS adapters without needing to rename public editor concepts.
