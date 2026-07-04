# `src/compiler_rust/compiler/src/codegen/instr/core.rs`_+_hir

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0002"></a>FR-DRIVER-0002 | Cranelift `>>` backend fix (disambiguation + signedness) | The `>>` operator is broken in the Rust bootstrap Cranelift backend (memory note `feedback_cranelift_shr_bug.md`). Root cause is two-part: 1. The HIR `BinOp` enum overloads `>>` as both `ShiftRight` and `Compose` (function composition — `sr | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
