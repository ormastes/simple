# Bug: RISC-V 64 full-kernel boot path fails rv64 codegen (interrupt.spl + privilege_bridge.spl)

**ID:** riscv64-kernel-codegen-blocker-2026-07-20
**Domain:** compiler/backend (rv64 MIR + codegen), os/simpleos
**Severity:** blocker (for the rv64 boot→login→ls→launch goal)
**Filed:** 2026-07-20

## Summary

The rv64 serial management shell (`login`/`ls`/`launch`) is implemented,
committed, and reachable on the boot path
(`entry.spl → kernel_main → Riscv64Boot.boot_main → os_main() → serial_shell_main`,
boot.spl:79-80). But the **full-kernel entry** (`examples/09_embedded/simple_os/arch/riscv64/entry.spl`)
fails to compile to a bootable rv64 ELF due to two pre-existing rv64 codegen
gaps in modules the full boot path transitively imports. The only rv64 entry
that *does* build (`smoke_entry.spl` / `fpga_serial_entry.spl`) uses
`rt_riscv_*` extern stubs and never reaches `boot_main`/`os_main`/`serial_shell_main`,
so it cannot exercise the interactive shell. Net: rv64 boot→login→ls→launch is
unverifiable until the rv64 codegen lowers the two constructs below.

## Evidence (build log, `bin/simple native-build --entry .../entry.spl --target riscv64-unknown-none`)

```
FAILED FILES (2):
  - src/os/kernel/arch/riscv64/interrupt.spl
      => mir: Unsupported HIR construct: complex lvalue: Deref(HirExpr { kind: Local(1), ty: TypeId(1761) })
  - src/os/kernel/privilege/privilege_bridge.spl
      => codegen: Module error: 1 function body/bodies failed to compile: [bridge_has_mirror]
         set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe — binary will silently misbehave)
Build failed: native-build aborted: 2 file(s) failed to compile
```

Also seen (non-fatal but indicative of weak rv64 module resolution):
`cannot resolve import: module path segment 'std' not found` (checked path
`src/os/crypto/std`) and `[DEBUG lower_lvalue] Unsupported lvalue kind: Deref(...)`.

## Root cause (two distinct gaps)

1. **Complex deref lvalue in MIR lowering** — `interrupt.spl` (and likely
   others) produce a `Deref(Local)` lvalue the rv64 cranelift path cannot lower.
   Same class as prior baremetal lowering gaps.
2. **`bridge_has_mirror` codegen failure** — `privilege_bridge.spl` function
   body fails codegen; the offered `SIMPLE_ALLOW_STUB_FALLBACK` escape hatch is
   explicitly unsafe ("binary will silently misbehave") and is NOT acceptable
   per the no-shortcut rule — the function must actually compile.

## Impact

- rv64 boot→login→ls→launch cannot be built/booted. The stub-based
  `smoke_entry` builds (22 KB) but is a probe, not the shell path, and its
  freestanding link also reports "2 unexpected unresolved symbol(s)".
- The serial shell source itself is correct and on the intended path; the
  blocker is purely the rv64 codegen's inability to compile the full kernel
  dependency closure.

## NOT a workaround

`SIMPLE_ALLOW_STUB_FALLBACK=1` would let it link but silently misbehave —
forbidden (no shortcuts). The fix is to make rv64 codegen lower (1) complex
deref lvalues and (2) `bridge_has_mirror`, or to refactor those two modules
to avoid the unsupported constructs.

## Related

- rv64 serial shell + login + ls: commit 6b87d996bf62
- rv64+rv32 launch command: commits cc5256812d48 / 8ef6c4c8a11a
- rv32 emission blocker: doc/08_tracking/bug/riscv32_cranelift_emission_blocker_2026-07-20.md
- Bidirectional serial harness (ready, pending a bootable ELF):
  scripts/qemu/check_simpleos_rv64_serial_shell.shs

## Update 2026-08-06: still blocked, gap moved further down the closure

Re-tried while pushing the riscv64 toolchain-payload boot campaign forward
(cross-built `bin/release/riscv64-unknown-simpleos/simple` userland payload
landed today, never booted — see
`doc/03_plan/os/simpleos/in_guest_simple_toolchain_multiarch_plan.md`). Built
directly with the Rust seed (mirroring the x86_64 UEFI harness pattern,
bypassing the `bin/simple os build` scenario runner — see the separate
harness-probe-timeout note below):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB="$(pwd)/src" src/compiler_rust/target/release/simple \
  native-build --source build/os/generated --source src/os --source src/lib \
  --backend cranelift --entry-closure \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld
```

The two 2026-07-20 blockers (`interrupt.spl` Deref lvalue,
`privilege_bridge.spl` `bridge_has_mirror`) are **not** what stops the build
now — the closure gets further before failing on a different file/symbol:

```
FAILED FILES (1):
  - src/os/kernel/ipc/cspace_spawn.spl => codegen: Module error: codegen:
    1 function body/bodies failed to compile: [SingleUseLedger.is_armed];
    set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe —
    binary will silently misbehave)
```

Root cause is visible earlier in the log:
`[CODEGEN-STUB-FALLBACK] body compilation failed for 'SingleUseLedger.is_armed':
ModuleError("... Unsupported feature: should be implemented in ISLE: inst =
\`v63 = vany_true.i64x2 v62\`, type = \`Some(types::I8)\`")` — the cranelift
rv64 backend has no ISLE lowering for a 128-bit `vany_true` vector-any-true
reduction. Same "not a workaround" rule applies: `SIMPLE_ALLOW_STUB_FALLBACK`
is explicitly unsafe and was not used. Net: rv64 full-kernel boot (and
therefore booting the cross-built toolchain payload) is still blocked purely
in the compiler backend — a real ISLE lowering gap for `vany_true.i64x2`, not
a riscv64-silicon or QEMU/OpenSBI issue.

## FIXED 2026-08-06: was compiler overgeneration, not a genuine ISLE gap

Investigated whether to add a riscv64 ISLE lowering rule for `vany_true.i64x2`.
It is not possible/appropriate: `src/compiler_rust/vendor/cranelift-codegen/src/isa/riscv64/lower.isle`
already has a general `vany_true` rule (line 2778), gated by `(ty_supported_vec
ty)`. `ty_supported_vec` (`src/compiler_rust/vendor/cranelift-codegen/src/isa/riscv64/lower/isle.rs:185`)
requires `ty_vec_fits_in_register`, which requires `ty.bits() <=
min_vec_reg_size()` — and `min_vec_reg_size()` is `0` on a bare riscv64 target
with no `V` extension. So **no** vector type, of any lane width, can ever match
that rule on this target: there is no vector register file to lower onto, and
adding an i64x2-specific ISLE rule would be lowering vectors onto hardware that
doesn't exist.

The actual root cause: `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
hand-inlines two numeric intrinsics — `compile_inline_numeric_contains_u64`
(`rt_numeric_contains_u64[_data]`, called for `SingleUseLedger.is_armed`'s
`token_ids[i] == token_id` scan) and `compile_inline_numeric_xor_sum_u64`
(`rt_numeric_xor_sum_u64[_data]`) — and both **unconditionally** emitted
explicit `I64X2` SIMD (`splat`/`load.i64x2`/`bxor`/`vany_true`) with no check of
what the target ISA actually supports. This is MIR/codegen overgeneration, not
a lowering gap: any 2-lane u64 SIMD-any-true/reduce for a scalar array-of-u64
should scalarize on a target with no vector unit.

**Fix landed:** both functions now check
`ctx.module.isa().triple().architecture` and only take the I64X2 SIMD fast path
on `X86_64` (SSE2 baseline) / `Aarch64` (NEON baseline), which are guaranteed
to have real hardware support. Every other target (riscv64 without `V`,
`s390x`, `pulley`, etc.) falls back to a plain scalar per-element loop — for
`contains_u64` this reuses the existing tail-loop scalar body already present
for the "remainder" case; for `xor_sum_u64` a new
`compile_scalar_numeric_xor_sum_u64` helper mirrors the header/bounds-check
dance and applies the same `raw_data ? sum : sum << 3` result transform the
SIMD path used. x86_64/aarch64 codegen is byte-for-byte unchanged (same
instruction order under `use_simd == true`).

**Verified:** rebuilt the Rust seed and re-ran the exact riscv64 full-kernel
build command from the 2026-08-06 update above. Before the fix: `FAILED FILES
(1): cspace_spawn.spl => ... SingleUseLedger.is_armed ... vany_true.i64x2 ...
should be implemented in ISLE`. After the fix: **0 FAILED FILES** — every
`.spl` in the closure, including `cspace_spawn.spl`, now compiles and the build
reaches the link stage. Sabotage-tested: reverted `calls.rs` to the pre-fix
version, rebuilt, reran the identical command — the exact original
`SingleUseLedger.is_armed` / `vany_true.i64x2` "should be implemented in ISLE"
failure reproduced verbatim, then the fix was restored and re-verified.

**New blocker exposed further down (not fixed here, out of this task's scope):**
the build now fails at the **C inline-asm assembly stage**, not compile:
```
Build failed: compile inline asm C failed: .../simple_asm_blocks.c:445:12:
error: unrecognized instruction mnemonic, did you mean: c.li, c.lui, li, lui?
  "cli\n.Lhalt_loop:\nhlt\njmp .Lhalt_loop\n"
```
Pinned to `src/os/kernel/interrupts/idt.spl:230-235`, function `_halt()`:
```
fn _halt():
    """Disable interrupts and halt CPU forever."""
    asm """
        cli
        .Lhalt_loop:
        hlt
        jmp .Lhalt_loop
    """
```
`cli`/`hlt`/`jmp` are x86_64-only instructions with no riscv64 equivalent
mnemonics — this inline asm block is unconditionally compiled regardless of
target, meaning `idt.spl` (or something that imports it) is reachable from the
riscv64 boot entry-closure despite being x86_64-specific. This needs either
target-gating the `_halt()` asm block (per-arch halt implementations, mirroring
how `x86_64/cpu.spl` / `x86_32/cpu.spl` already have their own `hlt`/`x86_hlt`)
or fixing the import chain so riscv64 doesn't pull in this x86_64-only IDT
module at all. Left undone here as a distinct, unrelated bug class (bad-target
inline asm reachability, not compiler backend codegen) — filing as a new
tracked item is the next step rather than forcing a fix into this task.
