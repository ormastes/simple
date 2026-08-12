# SimpleOS direct-LFB blend-span QEMU gate — 2026-08-12

Status: **IMPLEMENTED / BOOT EVIDENCE BLOCKED**.

The x86_64 freestanding runtime now owns `rt_gui_blend_span4`, validates the
tagged source array and row bounds, and performs exact straight-alpha src-over
directly against the registered LFB. `FramebufferDriver` uses it only for an
oversized non-staged MMIO surface and falls back to portable per-pixel blending
when an architecture returns zero. Host-backed and staged surfaces continue to
use `rt_engine2d_simd_blend_span_u32`.

Focused hosted/interpreter parity passes. The canonical readiness command:

`sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs`

reports `skip`: QEMU q35/std-vga argument parsing succeeds, but
`SIMPLEOS_KERNEL_ELF` is unset/missing. Therefore no kernel, Direct-LFB call,
QMP screenshot, checksum, or 8K timing has been observed. A future evidence
run must provide a freshly built kernel ELF, reach the desktop serial marker,
capture scanout, and publish viewport/backend/revision/readback/p50/p95/RSS/
fallback/checksum fields. Static disassembly is not sufficient.

The static SIMD helper script also currently invokes GNU `objdump` with the
unsupported option `--disassemble-symbols`; that tooling defect is independent
of the rendering implementation and must not be reported as a kernel failure.
