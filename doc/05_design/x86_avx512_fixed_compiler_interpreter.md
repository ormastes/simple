# x86 AVX-512 Fixed-Width Compiler and Interpreter Design

The MIR operation is the shared semantic boundary. The interpreter evaluates lanes in language order. The x86 selector uses capability evidence to choose EVEX lowering for operations whose ordering permits it and keeps an explicit ordered scalar sequence where reordering changes observable results.

Gather uses ZMM dword indices for sixteen f32/i32 lanes and YMM dword indices widened for eight f64 lanes. Permute uses `VPERMPS`, `VPERMD`, or `VPERMQ`; reverse and interleave use generated control vectors and `VPERMI2D/Q`. Broadcast validates the scalar lane before splatting.

Floating sum/min/max reductions stay ordered because tree reduction changes rounding and NaN selection. Scatter stays ordered unless MIR eventually carries a verified uniqueness fact; AVX-512 scatter does not define a language-compatible winner for duplicate addresses. These are required semantic paths, not missing acceleration.

The encoder tests assert complete EVEX+opcode+ModRM/VSIB byte sequences. Integration tests assert selected pseudo-op families before register allocation and successful final encoding. Capability denial and malformed operands remain negative gates.
