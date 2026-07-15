# Showcase apps agent tasks

- 2D sidecar: inventory primitives and dummy paths; propose Engine2D/readback coverage. Completed read-only and reviewed by root.
- Web sidecar: inventory HTML/CSS and browser/WM gaps; propose standards page and interaction checks. Completed read-only and reviewed by root.
- GUI/integration sidecar: inventory catalog, SimpleOS, docs, skills, and manuals. Completed read-only and reviewed by root.
- Merge owner: root agent.
- Final reviewer: root/highest available model; broad findings and exclusions require direct source/test evidence.

Concurrent compositor files remain owned by another active lane. Integration proceeds through clean catalog/app/docs/tests first and merges compositor changes only after ownership is clear.

## Status (2026-07-15) — verified surface × app matrix

| App | Standalone | Host-WM | SimpleOS WM |
|-----|-----------|---------|-------------|
| 2D showcase | ✅ 320×240 anti-fake gate passes (720p interpreter-timeout) | ✅ `wm_2d_child.ppm` 1473 colors, 99.998% nonzero | ⛔ blocked (compiler bug, see below) |
| Widget/GUI showcase | ✅ `widget_showcase_720p.ppm` 15-color vector UI | ✅ `wm_widget_child.ppm` live widget state | ⛔ blocked (compiler bug) |
| Web browser showcase | ✅ CSS/layout/paint engine proven `realeng_640.ppm` 8 source-matching colors; full-text render toolchain-gated | — | ⛔ blocked (compiler bug) |

**Verified: 5 surface cells** with real pixels. Dummy-impl audit done (3 fakes filed). Docs/guide/spipe skill updated + pushed.

### SimpleOS WM surface — 6 blockers cleared, 7th root-caused
Boot advanced from crash → boots fully through pmm/vmm/vfs/framebuffer/4K-scanout/engine2d/input/compositor/shell-init → **reaches the paint call**. Fixes landed: O(n²) framebuffer alloc (`1fe2653d`), compositor native-build (`3e5ef0c9`), font-load degrade guard (`c0f5d02f`), two spawn `Option`-nil miscompiles (`e8c4c3b1`/`f09dadd6`, faults 165→2), baremetal mutex halt (`ff302353`), executor scalar-dim workaround (`05102c73`).

**Remaining blocker:** native-build cross-module **field-resolution** bug (reads `FramebufferDriver.width`/`TaskbarModel.revision` shifted 1 slot). Array-slot hypothesis **disproven** (minimal repro resolves correctly on the exact live target); it's a full-graph name-keyed heuristic collision in the type-inference-less native path (`resolve_field_index`, function_lowering.spl:582). Bug doc `simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md` has a drop-in `[FIDX]` diagnostic + one-compile pin procedure. **Env note:** pinning/fixing needs a compiler rebuild; this Mac's bootstrap Stage-1 link fails (`-lSystem`/`_main_shim.o`). **Current directive: fix the Mac bootstrap-link to unblock rebuild, then pin + fix + verify the SimpleOS render (in progress).**

### Toolchain-gated (not app logic)
Web full-text glyph render: seed can't JIT the 17MB font sfnt path; deployed binary blocked by `rt_cli_arg_count`. Needs seed HIR fix or Stage-4 redeploy.
