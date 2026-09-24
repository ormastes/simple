# x86 AVX-512 Fixed-Width Compiler and Interpreter Requirements

This narrows the accepted SIMD bootstrap requirements to the first isolated AVX-512 compiler/interpreter delivery.

## Functional requirements

- **REQ-AVX512-001:** Interpreter semantics cover fixed `Vec16f`, `Vec8d`, and `Vec16i` arithmetic, unary and ternary operations, comparisons, masks, select, splat, load/store, gather, scatter, permute, shuffle, and reductions.
- **REQ-AVX512-002:** A capability-qualified x86-64 backend emits AVX-512F EVEX instructions for supported fixed-width operations, including f32/f64/i32 gather and permute.
- **REQ-AVX512-003:** Reverse, both interleave halves, and broadcast-lane preserve lane order and bounds behavior.
- **REQ-AVX512-004:** Floating reductions retain ordered lane evaluation so rounding and NaN behavior match the interpreter.
- **REQ-AVX512-005:** Scatter retains ascending-lane writes when index uniqueness is not proven, so duplicate indices deterministically leave the highest-lane value.
- **REQ-AVX512-006:** Unsupported capability and malformed encoding inputs fail closed.

## Acceptance

Interpreter behavior tests are the semantic oracle. Native selector tests prove operation-family selection, and complete-byte encoder goldens prove EVEX fields rather than matching an opcode byte in isolation. Native execution and performance remain blocked until a qualified AVX-512F host is available.
