# LLVM pointer-valued integer constants

The actual optional-array cycle3 failed before object generation with retained
`add ptr 3` IR. Its separate HIR/nil-copy proposals remain held and its three
feature-cycle cap is unchanged. This change repairs the general backend
constant contract rather than modifying those source lowering proposals.

`MirToLlvm.llvm_type_text` maps Array, Slice, Struct, Enum, Tuple, Dict, Union,
Ref and other pointer families to LLVM `ptr`. `translate_const` previously
emitted every `MirConstValue.Int` with `add`, including already registered
pointer destinations and fresh SSA destinations without `MirLocal` entries.
An LLVM pointer cannot be the operand type of integer `add`.

The instruction now defines a pointer-valued integer word with target-native
`inttoptr`, registers pointer bookkeeping and retains the existing local,
value-type and defined-local records. This dispatch uses the actual selected
LLVM type, so it covers both MIR aggregate types and a registered pointer
destination receiving a raw MIR integer word. Scalar integer definitions keep
their existing integer arithmetic encoding.

Both typed operand renderers and typed static initializers now use an LLVM
`inttoptr (...)` constant expression for pointer-valued Int words. Raw pointer
Zero renders as `null`; tagged nil Int(3) stays pointer word 3, never null.
The deliberately untyped initializer/string helper remains unchanged. Text
boxing, Boolean/float variants, pointer copy/move and explicit Cast lowering
retain their existing contracts.

MIR stores integer literals as i64 even when generating a 32-bit target.
Pointer constants use the signed low32 spelling on such targets, preserving
the target word/tag bits while avoiding an out-of-width integer token. On
64-bit targets the full i64 word is retained. This follows LLVM's integer to
pointer width semantics; it does not assert that an arbitrary tagged/numeric
word is dereferenceable. See the [LLVM inttoptr contract](https://llvm.org/docs/LangRef.html#inttoptr-to-instruction).

An Int constant assigned a floating or void LLVM type is not silently treated
as a floating payload or a numeric conversion. It records
`E-BACKEND-LLVM-CONST-TYPE` through the existing fail-closed generator error
owner. An explicit MIR Cast remains the numeric conversion operation. The
existing module error envelope prevents object generation from such output.

The new eight-scenario SSpec file calls the actual generator. Its matrix
covers the eight requested aggregate/reference families plus Ptr, raw zero,
nil3, other positive/negative words, native32/native64, wide-word truncation,
fresh and registered destination records, typed ordinary/indexed operands,
full MIR module/global generation, Copy/Move/Cast roundtrips, signed/unsigned/
char/bool/float scalar controls, explicit integer-to-float Cast and malformed
integer-to-float/void refusal. Tests are authored and UNEXECUTED. No LLVM
assembler, native producer compile, link or executable run occurred.

Validation is source-only guard/diff checks and inspection of the existing
mapper, copy/cast and error owners. Full compiler qualification requires the
root-serialized admitted producer and real LLVM verification/execution. This
is not evidence of optional-array success, full CLI memory repair or an RSS
improvement; the six other optional-array consumers remain independently open.
