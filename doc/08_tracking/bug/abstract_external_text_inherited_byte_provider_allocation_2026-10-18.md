# Inherited raw text/byte provider allocation result is not typed

Status: OPEN, discovered during abstract/external text implementation; root integration owner must qualify or repair the provider before claiming universal allocation-safe host conversion.

`src/lib/common/text_bytes.spl` existing text_to_utf8_bytes returns [u8], and its existing rt_text_to_bytes runtime provider can return a null/invalid array on allocation failure. The existing bytes_to_text also returns text directly and may return its allocation-failure sentinel. This feature adds a fallible packed byte allocator and propagates its errors throughout owned external buffers/codec/carry, but cannot infer success from the old unchecked provider signatures. No allocation-failure injection was run.

Reproduction gate: inject provider allocation failure on internal-text byte extraction and final UTF-8 Text materialization; require a typed error with no empty-text substitution or partial output. Reuse an admitted native runtime and existing failure-injection mechanism; do not stress the machine into OOM or invent a new C/Rust runner.

Generic [u8] literals/push arrays are not automatically packed. The new owner explicitly uses existing rt_byte_array_new and the tests verify native bytes-basis length. That storage gate is separate from the inherited text provider failure contract.

## Prerequisite landing scope

The checked extraction guard now rejects null backing storage and exact-length mismatch through TextByteBufferError. The deterministic mismatch spec is not OOM injection. Final bytes_to_text materialization remains unchecked, and future foundation/session error propagation is outside this landing. Native/provider/allocator execution remains UNRUN; this issue is not closed.
