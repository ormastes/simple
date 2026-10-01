# SimpleOS WM QEMU Evidence Wrapper Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl`

Six scenarios inspect the production wrapper without booting QEMU.

## Operator flow

1. Invalidate cached kernels when owned SimpleOS sources change.
2. Derive `pmemsave` address, stride, dimensions, and bounds from validated
   guest scanout metadata.
3. Capture the canonical taskbar-clock rightmost 56×48 slot (8,064 RGB bytes).
4. Keep the expected font-region hash empty until a trusted retained capture;
   after it matches, require the guest marker to bind the Noto Sans Mono asset
   hash, pure `glyf` rasterizer, Draw IR route, size, text, crop, and crop hash.
5. Drive QMP input, correlate the host nonce with monotonic guest input
   sequence, and prove F11 maximize/restore.
6. Fail closed on malformed QMP replies, capture errors, invalid geometry, or
   missing correlation.

The executable spec is authoritative; runtime pixel promotion remains pending.
