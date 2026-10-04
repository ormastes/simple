# LLVM shared-dispatch tagged payload extraction

The 7a98 bootstrap producer compiled the same nine-case Result<bool> fixture with frozen 9737 CoreC runtime. Cranelift passed all nine; LLVM compiled successfully then returned 42 with seven failed checked-unwrapping, nested Result and actual boolean record-field assertions. The direct branch and Err propagation passed, so a branch-only test concealed the representation defect.

LLVM emitter.rs::emit_unbox_int shifted every integer-shaped value by three. Its shared dispatch bypassed the legacy functions.rs tag-aware extraction. Tagged false 19 and true 11 were therefore decoded inconsistently with the runtime. The new shared build_unbox_int_value preserves the existing legacy 64-bit runtime helper and non-64-bit tag handling, and both paths call it. Non-integer trait values still pass through unchanged.

Focused native baseline receipts are retained in runtime/windows-restart-20261004/result-bool-try-{baseline1,llvm-baseline1}. This is bootstrap diagnostic evidence, not admission. Corrected-seed execution and Rust regression are pending. The actual policy InvalidPolicy causal connection remains pending until its roundtrip passes with corrected generated code.
