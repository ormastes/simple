# GPU and SIMD Specification

**Version:** 2025-12-26 Update (Vulkan Backend)
**Scope:** Language + standard runtime contracts (portable semantics; backend-specific lowering is non-normative)

This document specifies GPU compute and SIMD vector operations for the Simple language.

## Recent Updates (2025-12-26)

- **Vulkan/SPIR-V Backend**: Implemented cross-platform GPU compute backend
  - SPIR-V 1.3 bytecode generation for Vulkan 1.1+
  - Full type system support (i32, i64, u32, u64, f32, f64, bool)
  - Control flow (if/else, loops, returns)
  - Multi-type buffer parameters with descriptor sets
  - Array indexing and element access
  - GPU built-ins (thread IDs, barriers, atomics)
- **Enhanced Specification**: Added Vulkan usage examples and backend selection documentation

## Design Philosophy

Simple's GPU/SIMD support follows these principles:

1. **Safety First**: All operations are bounds-checked by default
2. **Explicit Parallelism**: No hidden data races or undefined behavior
3. **Portability**: Abstract over different hardware (CPU SIMD, GPU compute)
4. **Integration**: Works seamlessly with existing type system and memory model
5. **One-pass Parsable**: All constructs recognizable with bounded lookahead
6. **No GPU GC**: Kernels are GC-free; device allocations must be explicit or value-only

---

