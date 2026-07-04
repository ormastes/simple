# Production GUI Web Renderer Parity Hardening NFRs

## NFRs

- NFR-001: Pixel parity for this slice is exact: mismatch count must be `0`,
  match percentage must be `10000`, and max channel delta must be `0`.
- NFR-002: The parity harness must not use blur, perceptual tolerance, or
  fixture-mode fallback.
- NFR-003: The renderer dispatch must prefer generic layout rendering for
  generated GUI widget HTML so app HTML does not silently enter heuristic
  rectangle shortcuts.
- NFR-004: Evidence must be deterministic at a fixed viewport size.
- NFR-005: Verification must be runnable without GUI access or external browser
  processes for this first backend-parity slice.
- NFR-006: Follow-on Electron/WebKit slices must record capture provenance,
  viewport, color format, tolerance policy, mismatch count, and artifact paths.
- NFR-007: Electron generated-GUI evidence must distinguish `pass`,
  `divergent`, `fail`, and `unavailable`; a divergent measured result is valid
  diagnostic evidence but not completion of Electron parity.
