# Engine2D Four-Backend Capture NFR

- **NFR-E2D4-001:** Every evidence record is bound to an exact source revision.
- **NFR-E2D4-002:** A focused target is launched at most once per verification
  cycle, with no more than three fix/verification cycles.
- **NFR-E2D4-003:** Captures use the same physical dimensions. Host captures
  use 300 DPI; QEMU records its framebuffer DPI metadata explicitly.
- **NFR-E2D4-004:** Pixel comparison never hides geometry or event mismatches
  behind a visual tolerance.
- **NFR-E2D4-005:** Runtime evidence records elapsed time and peak RSS when the
  platform wrapper exposes them.
- **NFR-E2D4-006:** Backend adapters do not place transient atlas, cache, or GPU
  resource material in Draw IR.
