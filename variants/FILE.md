# variants/ Manifest

Module-variant-override overlays. Selected by explicit `variant:`/`platform:`
build configuration to override a base seam file (e.g.
`src/lib/nogc_sync_mut/target_ext.spl`,
`src/lib/gc_async_mut/gpu/engine2d/renderer_select.spl`) with a fixed,
target-specific implementation. Default/`auto` builds never load these —
they fall back to runtime host detection in the base seam. Enforced by
`scripts/check-workspace-root-guard.shs`.

## Allowed Entries

| Entry | Description |
|---|---|
| `__init__.spl` | Package marker |
| `platform` | Platform build-extension overlays (`linux`/`mac`/`windows`) for `nogc_sync_mut/target_ext.spl` |
| `ui` | UI renderer-selection overlays (`cpu`/`metal`/`vulkan`/`webgpu`) for `gpu/engine2d/renderer_select.spl` |
| `FILE.md` | This manifest |
