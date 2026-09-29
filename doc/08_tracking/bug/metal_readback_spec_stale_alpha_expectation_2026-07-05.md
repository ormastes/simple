---
id: metal_readback_spec_stale_alpha_expectation_2026-07-05
status: FIXED
severity: medium
discovered: 2026-07-05
discovered_by: Gate run of scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs during draw_image GPU-dispatch work
related: test/02_integration/rendering/metal_engine2d_readback_spec.spl
related: src/lib/gc_async_mut/gpu/engine2d/backend_software.spl
related: src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl
---

# metal_engine2d_readback_spec expects pre-blend overwrite; rect fill now alpha-blends (spec stale, not a readback bug)

## Summary

`metal_engine2d_readback_spec.spl` ("downloads clear and rect_filled pixels from
the Metal framebuffer") fails:

```
expected 270479167 to equal 16909060
```

i.e. `pixels[68]` (the (4,4) corner of the filled rect) is `0x101F2F3F`, not the
rect color `0x01020304`. This makes
`scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs` report
`status=fail / reason=missing-native-metal-framebuffer-readback-proof`.

## Root cause

Commit `97e3699cd3` (2026-07-04, "wip: working-copy snapshot (hourly sync)")
added alpha-aware rect fills to BOTH lanes:

- CPU mirror: `sw_hline_blend` path when `color_a(color) < 255`
  (`backend_software.spl:156-164`)
- Metal: `blend_src_over` Porter-Duff src-over in the rect_filled kernel
  (`backend_metal_msl.spl:160-211`), documented there as "bit-identical to the
  CPU reference blend()"

The spec's rect color `0x01020304` has alpha `0x01`, so it now blends over the
clear color `0x10203040`: each channel `(src*1 + dst*254)/255` →
`0x20→0x1F, 0x30→0x2F, 0x40→0x3F` = `0x101F2F3F`. The spec expectation
(`backend_metal.spl` overwrite semantics from before 97e3699cd3) was never
updated.

## Evidence it is NOT a GPU/readback regression

Probe (16x16, clear `0x10203040` + rect_filled `0x01020304`, interpreter,
2026-07-05):

- `gpu_frame_complete=true`, `source=device_readback`
- `pixels[68] == mirror[68] == 0x101F2F3F`
- GPU-vs-mirror full-frame diff count: **0** (bit-exact parity)

The failure also reproduces identically with the 2026-07-05 `draw_image` GPU
dispatch change reverted, and `git log -S` shows no readback-path change since
the blend landed. The device readback lane is healthy; only the spec constant
is stale.

## Fix options

1. Update the spec to use an opaque rect color (e.g. `0xFF020304`) and expect
   overwrite, or
2. Keep `0x01020304` and expect the blended value `0x101F2F3F` (pins the blend
   contract).

Option 1 preserves the spec's original intent (raw framebuffer download proof);
option 2 additionally pins src-over parity. Either restores the
`check-metal-engine2d-framebuffer-readback-evidence.shs` gate.

## Resolution (2026-07-05)

Fixed by combining both options in `metal_engine2d_readback_spec.spl`: the
original rect at `(4,4,4,4)` now uses an opaque color (`0xFF020304`, alpha=0xFF)
and expects overwrite — preserving the spec's raw-download intent — and a new
non-overlapping rect at `(8,8,4,4)` uses the original semi-transparent
`0x01020304` and expects the computed blended value `0x101F2F3F`, pinning the
src-over parity contract. `bin/simple test` on the spec and
`scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs` both
pass (`status=pass`, `gpu_readback_available=true`,
`blur_or_tolerance_used=false`). No backend code changed.
