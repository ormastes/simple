# Stage 3 VhdlProcessKind enum payload owner conflict

## Status

Resolved in source on 2026-08-04. Bootstrap cycles 1 through 3 passed this
former conflict and advanced to later monomorphization blockers. Full Stage 4
and QEMU admission remain blocked separately.

## Exact failure

The current-source Stage 3 build parsed all 542 closure sources and completed
HIR lowering before failing normally at monomorphization:

```text
phase3:hir_typecheck:done
phase4:monomorphize:start
[ERROR] phase 4 FAILED
error: in-process native-build: HIR lowering error in
src/compiler/backend/backend/vhdl_backend.spl: enum payload dependency
`VhdlProcessKind` conflicts:
`compiler.mir.mir_instruction_support::VhdlProcessKind::enum` vs
`compiler.backend.backend.hardware_codegen_types::VhdlProcessKind::enum`
```

Authority:

- source revision: `4ad6f949e9241ed445d635cf33195f9eb1897065` plus the retained
  working-copy diff captured by the bootstrap transcript;
- Stage 2 candidate source/build log:
  `build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`;
- Stage 3 log:
  `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`;
- wrapper log: `build/bootstrap-clang-23-1-stage4-current-cycle3.out`.

## Ownership and next bounded fix

Owned source currently declares the same public enum name in at least three
places:

- `src/compiler/50.mir/mir_instruction_support.spl`;
- `src/compiler/70.backend/backend/hardware_codegen_types.spl`;
- `src/compiler/70.backend/backend/common/hardware_codegen.spl`.

The next fresh session must select one canonical enum owner and make the MIR,
VHDL, LLVM/C backend, facade export, and hardware-codegen trait surfaces import
that identity. Do not suppress the dependency conflict or rename only the
diagnostic: enum payload ABI identity must be singular across the closure.

Required regressions are an exact Stage 2-to-Stage 3 bootstrap that reaches
monomorphization past this module and an adjacent focused compile that moves a
`VhdlProcessKind` payload through both MIR and `HardwareCodegen.compile_process`
without duplicate enum-owner dependencies. Only then may a fresh Stage 4 and
the LLVM-default SimpleOS QEMU gate resume.
