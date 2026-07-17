# SimpleOS Production Desktop Render Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl`

Five source-contract scenarios keep x86_64, AArch64, and RV64 desktops on the
canonical WM/Draw IR/Engine2D route.

## Operator flow

1. Mount the existing ARM FAT32 media where required, then register the selected
   VFS font bytes through the shared desktop bootstrap before Engine2D creation
   on x86_64 and AArch64.
2. Require the taskbar-clock `SharedWmScene -> DrawIrComposition -> Engine2D`
   marker to bind the selected asset hash, rasterizer, size, text, and crop hash.
3. Reject private post-frame `draw_text`, probe rectangle, or `present`
   paths.
4. Keep AArch64 and RV64 production entries on their canonical Engine2D owners
   and optional host-GPU presentation facades.
5. Submit one composed WM Draw IR frame to validated host presentation before
   local fallback.

The AArch64 canonical QEMU targets reuse their existing VirtIO-BLK disk
arguments and scenario image builder. Bitmap fallback remains only for failed
media mount or selected-byte validation. RV64 retains its unchanged bitmap path:
the available initializer is ARM-only and its 64 KiB runtime heap cannot carry
this vector-font bootstrap, so this contract makes no RV64 vector-font claim.
These are wiring assertions, not retained QEMU pixel evidence.
