# LLM Caret GUI Backends — Feature Requirements

The user selected both requested production paths.

- REQ-001: `bin/caret --provider dummy --electron` launches a real Electron
  `BrowserWindow` containing the Caret chat surface.
- REQ-002: Electron prompt submission routes through Caret's dummy provider and
  visibly renders `hello`.
- REQ-003: `bin/caret --provider dummy --metal-gui` launches a real pure-Simple
  winit window.
- REQ-004: The native surface generates semantic Caret HTML and lowers through
  Simple Web to a non-empty `DrawIrComposition`.
- REQ-005: The native surface explicitly selects Engine2D Metal and rejects
  unavailable, mirror-only, blank, or incomplete device output.
- REQ-006: Keyboard input and Enter submission update the native semantic state
  and visibly render `hello` from the same dummy provider contract.
- REQ-007: Existing CLI, TUI, and browser GUI behavior remains available.
