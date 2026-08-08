# Stage2 self-hosted binary segfaults in VulkanBackend.init; seed interprets it correctly

- **ID:** stage2_binary_vulkan_backend_init_segfault_2026-08-09
- **Status:** OPEN
- **Found by:** gui/web/2D vulkan showcase sweep, 2026-08-09
- **Area:** pure-Simple self-hosted runtime (stage2 authority binary) ×
  `std.gpu.engine2d.backend_vulkan` SFFI path
- **Severity:** high for the self-hosted lane — any engine2d Vulkan render
  under `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple`
  crashes; the same source runs correctly under the Rust seed

## Symptom

`web_standards_showcase_gui.spl` with `SIMPLE_GUI_BACKEND=vulkan` exits
silently with code 101 (no error line, log ends after module-init warnings)
under the stage2 binary. Minimal reproducer exits 139 (SIGSEGV):

```simple
use std.gpu.engine2d.backend_vulkan.{VulkanBackend}
fn main() -> i64:
    var backend = VulkanBackend.create()
    if not backend.init(64, 64):        # <- segfaults here (stage2)
        return 1
    backend.clear(0xFF204060u32)
    backend.draw_rect_filled(8, 8, 16, 16, 0xFFCC3020u32)
    val px = backend.read_pixels()
    if px[16 * 64 + 16] == 0xFFCC3020u32 and px[0] == 0xFF204060u32:
        print "VK_PROBE PASS"
        return 0
    3
```

## Control (same probe, Rust seed
`src/compiler_rust/target/bootstrap/simple` after the 2026-08-09
flat-namespace fixes)

No crash; `VK_PROBE PASS` — init/clear/rect/readback all correct on the
llvmpipe device. So the Vulkan backend and its SFFI bindings are sound; the
defect is in the stage2 binary's execution of this path (its interpreter or
the code it JITs — the probe logs the known
`Engine2DReadback.device_identity` HIR field-inference fallback first, so the
module runs interpreted in both binaries).

## Notes

- The stage2 binary predates the 2026-08-09 seed fixes; the pure-Simple
  compiler likely carries the same flat-registry assumptions
  (seed_flat_namespace_trait_struct_collision_2026-08-09). Whether this
  segfault is that same family or a separate runtime bug is undiagnosed —
  the self-hosted redeploy is blocked by the bootstrap repair lane, so no
  fixed self-hosted binary exists to bisect with.
- The deployed `bin/simple` (2026-07-16) segfaults even on
  `run`-ing a hello-world — a separate, older staleness symptom.

## Repro

```
S=build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple
$S run /tmp/vk_probe2.spl        # exit 139, prints "create..." "init..." then dies
src/compiler_rust/target/bootstrap/simple run /tmp/vk_probe2.spl   # VK_PROBE PASS
```
