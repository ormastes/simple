# Legacy MIR struct layout ignores the lowering target (2026-11-04)

**Status:** fixed in the `work/thir-layout-20261104` PR (legacy path), shadow/typed wiring pending a Stage 3 run.
**Found by:** PR #6643's agent (TargetHIR wire unit).

## Defect
`src/compiler/50.mir/_MirLowering/module_lowering.spl` called
`compute_struct_layout(fields, attr)` (`30.types/_TypeLayout/layout_core.spl:575`)
in `canonical_layout_digest`, `lower_struct_type` and `lower_class_type`. That
function uses a fixed LP64 table (`usize`/pointer/named = 8, `i64`/`f64` align 8)
regardless of `MirLowering.target_context`. Any 32-bit lowering target
(x86, arm, riscv32) got 64-bit field offsets and sizes in `MirFieldDef.offset`.

Example `struct { tag: u8, p: ptr, n: i64 }` repr(C) on riscv32:
legacy offsets 0/8/16 size 24; correct 0/4/8 size 16.

## Fix
`mir_target_aware_struct_layout(target, fields, attr)` in
`50.mir/mir_target_hir_layout.spl`: 64-bit targets (and unknown) keep the exact
legacy call (host-native builds byte-identical); x86/arm/riscv32 use
`compute_struct_layout_for_arch`. The TargetHIR reader is then wired behind
`SIMPLE_TARGET_HIR_MODE` (shadow mismatch fatal).

## Evidence
`test/01_unit/compiler/50.mir/mir_target_hir_layout_live_spec.spl` — 4/4 pass
(host snapshot, rv32 vs x86_64/aarch64 offsets, legacy/shadow/typed agreement,
injected LP64 layout caught in shadow). No Stage 3 compile of a cross target yet.
