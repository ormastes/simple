# Hosted riscv32 Linux native-build is unsupported (fail-closed)

- Status: open
- Severity: P3
- Found: 2026-11-20 (ubuntu-p2 cross matrix: row linux-rv32 `riscv32-unknown-linux-gnu` cannot build lint/test-runner)
- Component: compiler native link (`src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl`)

## Observation
The surface symptom was rustup having no prebuilt std for `riscv32gc-unknown-linux-gnu`, but that only came from the
lane script building the Rust `simple-native-all` runtime. The real gap is in the compiler: hosted RV32 is deliberately
fail-closed. `native-build` prints `host C runtime/entry compilation unsupported: target 'riscv32-unknown-linux-gnu'`.
Bare-metal RV32 objects are supported.

## Evidence
- `llvm_native_link_orchestrator.spl:253` emits the "host C runtime/entry compilation unsupported" error.
- `scripts/check/check-llvm-simd-row-native-arch.shs:184` `check_unsupported_riscv32_hosted` pins the rejection.
- `scripts/check/check-bootstrap-portability.shs:877` requires that check to be invoked (body checked just below).
- `doc/06_spec/01_unit/compiler/backend/hosted_c_target_guard_spec.md:381` "fails hosted RV32 closed without borrowing an RV64 toolchain".

## What is needed
An owner decision on whether hosted rv32 Linux is in scope. If yes: a hosted rv32 C runtime/entry plus a cross C toolchain
(`clang --target=riscv32-linux-gnu`, rv32 libc sysroot, compiler-rt), then flip the three gates above.
No spec added: the existing rejection spec pins current behaviour.
