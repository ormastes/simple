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
