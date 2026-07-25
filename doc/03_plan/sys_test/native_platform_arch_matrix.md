# Native platform and architecture system-test plan

## Scope

Harden pure-Simple native-build evidence for Linux, macOS, Windows, FreeBSD,
ARM32, AArch64, RV32, and RV64. Rust-seed builds are bootstrap evidence only.
Hosted targets must execute; unsupported 32-bit hosted targets must fail closed
and instead produce target-correct relocatable objects where supported.

## Acceptance requirements

| ID | Requirement | Evidence |
|---|---|---|
| REQ-PLAT-001 | Default LLVM and explicit Cranelift are tested on every supported hosted OS/architecture. | Hosted matrix/CI receipt |
| REQ-PLAT-002 | Every accepted artifact is nonempty and has the requested class, type, and machine; ARM32/RV32 also prove their declared ABI. | Shared helpers plus target-specific flag/attribute checks |
| REQ-PLAT-003 | Every runnable target exits with the exact expected status and output where specified. | `require_runtime_exit` plus fixture output check |
| REQ-PLAT-004 | Zero selected cases, FAIL, XPASS, or interpreter fallback fail the matrix. | `native-smoke-matrix.shs` strict summary |
| REQ-PLAT-005 | Normal tooling uses a fresh pure-Simple binary with stub fallback disabled. | Command environment and compiler provenance |

## Evidence matrix

| Platform/architecture | LLVM | Cranelift | Required proof | Current state |
|---|---|---|---|---|
| Linux x86_64 | Hosted full matrix + full parity | Hosted full matrix | exact exit/output | Wired; fresh CI receipt pending |
| macOS x86_64 | Hosted full matrix | Hosted full matrix | exact exit/output | Wired; fresh CI receipt pending |
| macOS AArch64 | Hosted full matrix | Hosted full matrix | exact exit/output | Wired; fresh CI receipt pending |
| Windows x86_64 | Default hosted matrix | Hosted matrix | PE/COFF + exact exit | Cranelift wired; default-LLVM row remains open |
| Windows AArch64 | COFF object | COFF object | nonempty machine-correct object | LLVM row remains open |
| FreeBSD x86_64 | Full QEMU matrix | Scoped QEMU matrix | guest identity + exact exit/output | Wired; fresh `--full` receipt pending |
| Linux ARM32 | Relocatable object | Explicit unsupported rejection | ELF32 ARM hard-float | Wired; fresh receipt pending |
| Linux AArch64 | QEMU-user executable | QEMU-user executable | ELF64 AArch64 + exact exit/output | Wired; Cranelift CI execution must be mandatory |
| Bare-metal RV32 | Relocatable object | Explicit unsupported rejection | ELF32 RISC-V, RV32IMAC, soft-float | Wired; fresh receipt pending |
| Linux RV64 | QEMU-user executable | QEMU-user executable | ELF64 RISC-V + exact exit/output | Wired; Cranelift CI execution must be mandatory |

OpenBSD and NetBSD are excluded from completion until a VM/hosted runtime lane
exists; header compilation alone is not runtime evidence.

## Shared checker contract

- `platform_case(name, description, writer, expected_exit, xfail)`
- `require_nonempty_target_object(path)`
- `require_target_machine(readelf, path, elf_class, machine)` (class/type/machine)
- `require_runtime_exit(expected, command...)`

No helper may turn a missing artifact, timeout, signal, empty selection, XPASS,
or fallback into a pass.
ABI checks remain target-specific: ARM32 requires hard-float and RV32 requires
RV32IMAC soft-float. No broader ABI claim is inferred from the shared helper.

## Execution order

1. Shell syntax and helper self-check.
2. One focused native hosted case.
3. LLVM ARM32/RV32 object gates.
4. LLVM and Cranelift AArch64/RV64 QEMU-user gates.
5. Linux hosted matrix, then macOS and Windows hosted CI.
6. `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full`.
7. Full parity only after focused gates are green.

## Pass/fail and retained gaps

Pass requires every selected row to emit its strict success receipt. Skipped,
`continue-on-error`, `|| true`, missing-tool, or metadata-only rows are not
acceptance. Current source hardening is not a platform execution receipt.

The fresh pure-Simple compiler/parser gate, Windows default-LLVM/ARM64 LLVM,
mandatory Cranelift cross-execution, hosted CI reruns, and FreeBSD full QEMU
run remain open.

## Traceability

| Requirement | Test/check | Coverage |
|---|---|---|
| REQ-PLAT-001, 003, 004, 005 | `scripts/check/native-smoke-matrix.shs` | Hosted language matrix |
| REQ-PLAT-001, 003, 005 | `scripts/check/check-freebsd-bootstrap-qemu.shs` | FreeBSD hosted/QEMU |
| REQ-PLAT-002, 003, 005 | `scripts/check/check-llvm-simd-row-native-arch.shs` | LLVM ARM/AArch64/RISC-V |
| REQ-PLAT-002, 003, 005 | `scripts/check/check-cranelift-aot-aggregate-cross.shs` | Cranelift AArch64/RV64 and 32-bit rejection |
| REQ-PLAT-002, 003 | `scripts/check/native-target-assertions.shs` | Shared fail-closed primitives |
| REQ-PLAT-001–005 | `test/01_unit/os/native_build_compiler_provenance_spec.spl` | Source-contract regression |
