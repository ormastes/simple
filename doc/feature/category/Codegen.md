# Codegen

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-95"></a>95 | Buffer Pool | Reusable buffer pools for code generation. Reduces allocation overhead when compiling many modules by recycling buffers instead of deallocating. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/codegen_technical.md](../../codegen_technical.md#feature-95) |
| <a id="feature-96"></a>96 | Generator Codegen | Generator state machine code generation. Transforms generator functions with yield statements into resumable state machines with dispatcher entry blocks. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/codegen_technical.md](../../codegen_technical.md#feature-96) |
| <a id="feature-97"></a>97 | LLVM Backend | LLVM-based code generation backend for 32-bit architecture support and broader platform coverage. Uses same MIR and runtime FFI as Cranelift. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/codegen_technical.md](../../codegen_technical.md#feature-97) |
| <a id="feature-100"></a>100 | Cranelift Backend | Cranelift-based code generation backend for AOT and JIT compilation. Provides fast compilation with good runtime performance. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/codegen_technical.md](../../codegen_technical.md#feature-100) |
| <a id="feature-101"></a>101 | Native Binary Compilation | Standalone native binary generation using mold/lld/ld linkers with 4KB page-aligned code layout for optimal startup performance. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/research/binary_locality.md](../../research/binary_locality.md#feature-101) |
