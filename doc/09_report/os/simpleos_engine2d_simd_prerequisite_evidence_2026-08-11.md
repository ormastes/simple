# SimpleOS Engine2D SIMD prerequisite evidence — 2026-08-11

Status: STATIC KERNELS PRESENT; LIVE BARE EXECUTION STILL UNPROVEN.

The canonical static prerequisite gate initially failed because it invoked GNU
`objdump` with the unsupported LLVM-style `--disassemble-symbols` option. The
gate now selects architecture-specific disassemblers (`aarch64-linux-gnu-objdump`
and host `objdump` by default), checks their availability explicitly, and uses
the portable `--disassemble=<symbol>` form.

Fresh object inspection confirms:

- ARM64 `rt_gui_fill4`: `dup v0.4s` and `st1 {v0.4s}`;
- x86-64 `rt_gui_fill4`: `pshufd` and `movdqu`;
- both sources define enabled/hit/chunk/tail receipt functions.

The wrapper did not emit its terminal PASS line during the capped attempts,
although isolated checks of all four instruction regexes passed. It therefore
remains RED as an aggregate gate pending one fresh-session rerun; no pass is
inferred from component inspection.

This gate is static-only by design. It does not boot QEMU, prove guest SIMD
hits, capture scanout, or establish 8K/80. The live SimpleOS fullscreen gate
remains the required next evidence step after an admitted kernel build.
