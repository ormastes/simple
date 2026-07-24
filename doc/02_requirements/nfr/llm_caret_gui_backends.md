# LLM Caret GUI Backends — NFR Requirements

- NFR-001: Electron is a host adapter only; Caret remains the application and
  provider owner.
- NFR-002: Web output must pass through Web semantic/layout and Draw IR before
  Engine2D Metal execution.
- NFR-003: Metal evidence must report backend `metal`, device readback, a
  positive backend handle/device identity, full pixel count, and nonzero
  checksum.
- NFR-004: No placeholders, hardcoded test passes, private font path, or CPU
  fallback presented as Metal are permitted.
- NFR-005: Focused launch/action evidence must cover visible text, keyboard or
  pointer delivery, response state, nonblank pixels, and backend provenance.
- NFR-006: Changes must remain isolated from the concurrent WM/theme lane.
