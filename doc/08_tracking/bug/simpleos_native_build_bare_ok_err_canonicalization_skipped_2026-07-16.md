# Bug: bare `Ok(...)`/`Err(...)` canonicalization skipped in entry-closure native-build (NVMe/vfs boot modules)

- **Date:** 2026-07-16
- **Severity:** critical (blocks SimpleOS x86_64 disk mount → diskless desktop → black screen)
- **Component:** rust seed MIR lowering (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`)
- **Related:** `simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md` (SEPARATE bug — a seed carrying that field-index fix still reproduces this one)

## Symptom
Kernel built via `native-build --entry-closure` (gui_entry_desktop.spl, cranelift,
x86_64-unknown-none): serial shows 11 warnings `[WARN] unresolved fn: Ok` /
`unresolved fn: Err` — all in the NVMe/vfs boot path. NVMe init null-faults
(cr2=0x0) inside `NvmeDriver.init_from_grant` (fault RIPs map via `llvm-nm` to
`..._NvmeDriver_dot_init_from_grant` and `vfs_boot_init_pure_nvme_fat32`), then:

```
pure-nvme lease policy degraded nvme-fs-transfer-not-ready:missing-nvme-doorbells
[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs
... degraded-no-disk apps=0
```

Desktop reaches compositor/shell but empty; QMP screendump 0.34% non-black.

## Mechanism (proven by experiment)
1. HIR lowers bare `Ok(x)` → `Call(Global("Ok"))` (`hir/lower/expr/calls.rs:49-66`),
   expecting MIR to canonicalize.
2. MIR canonicalization `Global("Ok")`+1 arg → `MirInst::ResultOk`
   (`mir/lower/lowering_expr_call.rs:208-233`) does NOT fire for the NVMe/vfs
   closure modules — the call stays a generic call to a symbol literally named `Ok`.
3. Cranelift emits `rt_function_not_found` (`codegen/instr/closures_structs.rs:816,829`;
   freestanding stub `baremetal_stubs.c:14406`) → returns NIL.
4. Result ops on NIL → null-fault in `init_from_grant`.

**Proof:** rewriting bare `Ok/Err` → qualified `Result.Ok/Result.Err` (different
HIR path, `static_enum_variant_type` at calls.rs:44) in `init_from_grant` +
`vfs_boot_init` advanced NVMe init one full stage
(`missing-nvme-doorbells` → `nvme-transfer-provider-not-simple`). Source-level
rewrite is whack-a-mole (Result is pervasive) — NOT an acceptable fix.

## Scope
Only the NVMe/vfs modules of the entry-closure build miscompile; the rest of
the kernel's Result usage (app-spawn, compositor) canonicalizes fine. Suspect
regression window: the Jul-13+ native-build closure-discovery / section-GC
churn (kernel shrank ~41 MB → ~12 MB). Suspect commit: `ca1e18c1744`
(last edit to `lowering_expr_call.rs`).

## Fix direction
In the seed: ensure `Global("Ok"/"Err"/"Some"/"None")` still canonicalize to
`Result*/Option*` MIR for functions pulled in via entry-closure discovery —
check whether the callee `Global` name is module-mangled away from the literal
`"Ok"`/`"Err"` before reaching `lowering_expr_call.rs:208`, and that
closure-discovery/section-GC doesn't skip the canonicalization pass for these
modules. Mirror any fix in the self-hosted compiler
(`src/compiler/50.mir/_MirLowering/`). Verify with a full clean kernel build +
QEMU boot: `unresolved fn: Ok|Err` count 11 → 0, fat32 mounts, apps > 0.

## Note (independent observation)
QMP `screendump` with `-vga std` captures the VGA device, while the desktop
renders to the baremetal framebuffer scanout (3840x2160) — verify the display
path when judging screendumps after this bug is fixed.
