# Production Host WM Fullscreen Evidence Contract

## Scope

This manual mirrors
`test/03_system/check/wm_production_fullscreen_evidence_spec.spl`.

## Required evidence

1. Reject Rust seed paths before any GUI launch.
2. Reject a missing explicitly selected production artifact.
3. Build and stage the winit, Rust runtime, and C runtime providers with
   relocatable macOS install names or ELF SONAMEs matching their staged names.
4. Link those providers directly into the native artifact with a relocatable
   loader path; do not rely on `DYLD_INSERT_LIBRARIES`.
5. Inspect the artifact load commands/dynamic section and reject a provider
   that is not linked.
6. Launch the production `src/os/hosted/hosted_entry.spl` artifact.
7. Correlate windowed, fullscreen, and restored scene snapshots with their
   presented framebuffer captures and input nonces.

The wrapper remains fail-closed: source markers, missing captures, stale
artifacts, synthetic receipts, and screenshots without framebuffer provenance
cannot pass.
