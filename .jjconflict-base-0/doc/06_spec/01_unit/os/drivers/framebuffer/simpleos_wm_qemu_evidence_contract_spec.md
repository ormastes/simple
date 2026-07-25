# SimpleOS WM QEMU Evidence Wrapper Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl`

Ten scenarios inspect the production wrapper without booting QEMU.

## Operator flow

1. Invalidate cached kernels when owned SimpleOS sources change.
2. Derive `pmemsave` address, stride, dimensions, and bounds from validated
   guest scanout metadata.
3. Capture the canonical taskbar-clock rightmost 56×48 slot (8,064 RGB bytes).
4. Require the retained production font-region SHA-256
   `addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc`
   and bind it to the guest Noto Sans Mono asset hash, pure `glyf` rasterizer,
   Draw IR route, size, text, and crop.
5. Drive QMP input, correlate the host nonce with monotonic guest input
   sequence, and prove F11 maximize/restore.
6. Fail closed on malformed QMP replies, capture errors, invalid geometry, or
   missing correlation.

The executable spec is authoritative; runtime pixel promotion remains pending.
