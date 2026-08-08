# Host 2D Vulkan/SIMD spec reds found during primitive-rendering verification

**Filed:** 2026-08-08 · **Severity:** mixed (see per-item) · **Scope:** HOST
(Linux x86_64) only, found while verifying
`doc/09_report/host_2d_vulkan_simd_primitive_verification_2026-08-08.md`.
**Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`,
mtime 2026-08-08 03:38 UTC. Vulkan device: llvmpipe (lavapipe, software),
the only device the loader enumerates headlessly in this sandbox.

These four `it` cases are correct specs asserting real behaviour the
implementation does not currently have (or, for #3/#4, source-scan checks
that are stale against the current file layout). Left RED per
`.claude/rules/testing.md` — not weakened, not marked pending.

## 1. Vulkan `draw_rect_filled` writes a wrong interior colour — high

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl:185,198`

```
it "draw_rect_filled leaves corners untouched":
    ...
    expect(pixel_at_p(pixels, 4, 4, 8)).to_equal(fg)   # line 198, fails
```

8×8 buffer, `clear(0x111111FF)`, `draw_rect_filled(2, 2, 4, 4, 0xAABBCCFF)`.
Pixel `(4,4)` — strictly interior to the filled region, not an edge — reads
`0xAF828DFF` instead of `0xAABBCCFF`. The two corner assertions in the same
test (`(0,0)` and `(7,7)`, both expecting the background colour) pass (the
failure message names only the fg-vs-observed comparison, not the bg
value), so: the clear/background path round-trips exactly, the fill path
does not, and the corruption pattern (`0xAA`→`0xAF`, `0xBB`→`0x82`,
`0xCC`→`0x8D`) is not a uniform channel shift. Mechanism undiagnosed.

**Unblock condition:** trace `draw_rect_filled`'s SPIR-V/GLSL path
(`backend_vulkan_spirv*.spl`, `backend_vulkan_glsl.spl`) for the interior
fragment-shading or descriptor-write step and compare against the
`draw_rect` (outline) path, which is unaffected per the same spec file's
passing cases.

## 2. Metal-on-Vulkan / DirectX-on-Vulkan emulation do not match the Vulkan reference — medium

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl:354,382`

Both `it` blocks assert the emulated backend's rendered buffer equals the
real-Vulkan reference buffer; both fail with `expected 2240 to equal 0`
(2240 mismatching values in the comparison, i.e. the buffers differ).

**Unblock condition:** diff the emulation-layer draw-call translation
(`backend_metal.spl` / `backend_directx.spl`) against the Vulkan reference
kernel invoked by `vulkan_compute_oracle_spec.spl`, isolate the first
divergent pixel.

## 3. `vulkan_engine2d_frame_batch_contract_spec.spl` fenced-submit dependency check — needs triage

`test/01_unit/check/vulkan_engine2d_frame_batch_contract_spec.spl:26`

`it "retains dependencies through the one fenced frame submit"` fails; not
triaged further in this pass (out of the fill/blend/blit/clear primitive
scope this report covers). Needs its own investigation pass.

## 4. `simd_kernels_spec.spl` MIR-source self-check is stale — low, not a rendering defect

`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl:108`

`it "uses the cross-mode return-array span bridge for backend fills"` reads
`mir_source` from a `file_read()` of a specific compiler source path and
`expect(mir_source).to_contain(...)`. The file it currently reads back is
`src/compiler/50.mir/mir_lowering_expr.spl`, which no longer contains the
`rt_engine2d_simd_fill_span_u32` dispatch string — a MIR-lowering file split
moved that string elsewhere. This is a source-layout staleness check, not a
pixel-correctness or rendering defect; it was pre-existing before this
task's spec additions (44/45 before, 50/51 after — the delta is the 6 new
cases added by this task, all passing).

**Unblock condition:** update the spec's `file_read()` target(s) to the
current file(s) containing the MIR dispatch string for
`rt_engine2d_simd_fill_span_u32` / `rt_engine2d_simd_copy_span_u32`.
