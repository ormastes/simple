# MirToLlvm trait-default overrides split into a second impl block are ambiguous (2026-10-24)

Symptom: Phase-3 module `compiler.backend._MirToLlvm.core_codegen` fails MIR with ~55
`unresolved method call: translate_X is ambiguous on ...class_def.MirToLlvm: impl blocks in more
than one module declare it` (aggregate, create_promise, await, yield, spawn, send, receive,
gpu_*, vhdl_*, simd_*; 27 methods).

Root cause: these methods have default bodies on trait `MirTextCodegen`
(`common/mir_text_codegen.spl`) and were overridden in an inherent `impl MirToLlvm:` in
`_MirToLlvm/aggregate_intrinsics.spl`, while the trait impl lives in `core_codegen.spl`. Not
duplicate text: the override and the trait default are two declarations in different modules.

Fix: moved the 27 overrides verbatim into `impl MirTextCodegen for MirToLlvm` in
`core_codegen.spl` (same pattern as the other overrides there); added the `GpuBarrierScope`
import. `llvm_emit_aggregate_impl` stays in the inherent impl. Unverified (no build allowed).

`len`/`unwrap` failures in core_codegen are the inferred-receiver class
(`mir_unresolved_method_inferred_receiver_2026-10-24`); left to the compiler fix.
