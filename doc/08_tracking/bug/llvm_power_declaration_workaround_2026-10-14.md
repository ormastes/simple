# LLVM power declaration workaround

The old d657 pure producer emitted integer __simple_pow and floating llvm.pow.f64 calls without declarations when compiling mir_instruction_graph. Saved LLVM IR and the prior retained-build llc failure establish the problem.

The graph now calls the existing i64 runtime power helper through an explicit typed unsafe ABI and uses the existing std.common.math.math math_pow wrapper for f64. These preserve the selected existing runtime operations; no power algorithm or overflow policy is reimplemented. The 20-case production mir_fold_binop native fixture is UNRUN until it links and executes.

The runtime header declares __simple_pow(i64,i64)->i64; core-c-bootstrap stages runtime_core_intrinsics and runtime_native C sources, with rt_math_pow calling libm pow. Rust Phase2 capsule archives do not supply __simple_pow. An exact new native link is still required to establish provider availability.

An optional future-emitter declaration patch was REJECTED by independent review: it duplicates llvm_backend's outer preamble, and the pre-existing 32-bit Pow/native_int ABI mismatch remains. That patch is not applied. Active emitter declaration ownership still needs a separate fix.

Limits: no signed-overflow/wrapping proof or 32-bit qualification; finite f64 cases only. The math_pow wrapper can add call overhead; this is an unmeasured performance risk, not a no-regression PASS. Identical compatibility fixes must be present in both collector baseline and candidate so its comparison isolates the lazy index change.
