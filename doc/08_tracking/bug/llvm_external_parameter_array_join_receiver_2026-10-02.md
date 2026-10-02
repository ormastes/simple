# LLVM external parameter array loses its join receiver

The Linux Phase 2 producer `184d1be492926713d19bfb95ba2705cb31a2fb6affe8ebea9e1874185d6ef921`, built from source `623b7943f1c8b61aa2d33144847c8d75c64b8fb7` with release bootstrap seed `4ad9c9f7444e625b384f5ceb6ea3144b126e5fc892a6e14e811313ba6f7c2992`, passes the ordinary and documented/exported class fixture through MIR but LLVM rejects `declare ptr @rt_alloc(nil)`.

The native disassembly identifies the cause in `MirToLlvm.external_declare_line`: the expression `param_tys.join(", ")` calls `lib__nogc_sync_mut__concurrent__thread__ThreadHandle_dot_join` at `0xd06017`, passing the separator as the only receiver. The returned value is then passed to `rt_value_to_string`, producing `nil` in the declaration. The source local was inferred from a dictionary lookup followed by `unwrap()` and lost its `[text]` receiver type in the bootstrap compiler.

The local repair preserves the declared dictionary element type explicitly with `val param_tys: [text] = recorded.unwrap()`. It does not replace an invalid LLVM type with a guessed fallback or special-case `rt_alloc`. The existing native class regression exercises aggregate allocation and therefore this external-declaration path.

The underlying bootstrap compiler defect remains separately actionable: receiver inference through `Dict<text, [text]>.get().unwrap()` must retain the array type, and unresolved method selection must never choose an unrelated same-named method. An explicit local type is a valid source annotation, not evidence that the general inference defect is fixed.

Evidence: `D:/dev/linux-mir-crash-20261002/class-after-184d/{stdout.log,rss.env,external-declare.asm}`. Compile exit 1 was a normal LLVM error, not a crash. The original loader regression was not dispatched after this failed gate. The advertised retained IR path was removed by the driver; the diagnostic log and native disassembly are retained.

Validation of the annotated source is pending a newly pinned Phase 2 build, native class execution, and the original loader closure. No native PASS is claimed yet.
