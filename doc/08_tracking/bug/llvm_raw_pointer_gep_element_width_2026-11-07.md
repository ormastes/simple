# LLVM raw pointer GEP loses pointee width

Status: source repair and executable regressions authored; runtime qualification pending an admitted rebuilt Pure-Simple producer.

## Reproducer and cause

A MIR function parameter `%l1: Ptr(U8, true)` followed by
`GetElementPtr(%l2, Copy(%l1), [Int(1)])` emitted
`%l2 = getelementptr ptr, ptr %l1, i64 1`. On x86-64 this advances eight
bytes rather than one. `Ptr(U16)`, `Ptr(I32)`, and `Ptr(F32)` also use the
wrong stride. Index zero cannot detect this defect.

The aggregate backend used `get_operand_type(base)` as the GEP element type.
That function intentionally maps every raw pointer/reference to LLVM's opaque
`ptr`; its result describes the address value, not the addressed element.

## Repair boundary

The class owner retains MIR Ptr/Ref element LLVM types keyed by emitted local
name. The normal function-local prepass records these types, synthetic copies
and moves inherit them, and pointer constants/casts/bitcasts record their explicit target.
GEP also recognizes typed constants and actual synthetic allocation element
metadata. Function reset clears the new map. Unknown bases retain the existing
fallback; runtime array/tuple/record layout is not inferred from their handles.
Single-index GEP results retain the same pointee type for synthetic chained
address calculations. Multi-index results keep their own declared leaf type.

Ownership is shared only in `core_codegen.spl`: this lane adds one call in the
local-declaration prepass, `translate_copy_move`, `translate_const`, and
`translate_alloc`; the parallel LLVM
call-owner lane owns its other edits. No historical or concurrent file is reset.

## Prevention and evidence limits

`test/01_unit/compiler/backend/llvm_gep_element_width_spec.spl` exercises real
MIR-to-LLVM translation with nonzero indices: byte, narrow integer, float,
machine integer, nested pointer and Ref parameters; synthetic copy/move aliases;
constant pointers; explicit casts/bitcasts; allocations; and function-state reset.
The expected IR directly distinguishes byte/word strides from pointer stride.

No interpreter, native executable, LLVM assembler, or full bootstrap PASS is
claimed by this source-only repair. The bootstrap owner must run these tests
with the admitted rebuilt producer and retain its identity and actual counts.
