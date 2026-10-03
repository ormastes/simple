# Loader text range and dictionary receiver lowering

Status: source candidates; executable verification UNRUN.

The U0002 loader closure completed eleven MIR modules on producer7cc and then
reported two range-index failures. Source correlation identifies the open-ended
text ranges in `src/lib/common/text_advanced.spl` indentation helpers (487,508).
The candidate lowers exclusive, unit-step text range indexing using the same
runtime byte-slice owners as colon slices. It proves text provenance after
evaluating the receiver once, fills omitted bounds with zero/length, and retains
loud errors for other collection, inclusive or stepped forms. The fixture
covers open/bounded/empty slices, array-element text and receiver side effects.

The same closure uses `CONTEXT_REGISTRY: Dict<i64, CompilerContextImpl>` and
invokes methods on extracted values. A runtime global is stored as an i64
handle. Imported-global PR2178 restores semantic Dict provenance, but the read
hook previously inspected only the builder type and the expression's optional
HIR type. It could still decode the returned class handle as an integer. The
candidate also consults retained local/declaration type evidence.

A second loss happens after decoding: canonical MIR Struct IDs are not HIR
symbol IDs. The dict read hook now uses `mir_struct_symbol_name`, matching the
already-qualified direct global read repair. It preserves owner-qualified
method/field identity without registering a duplicate class.

Native regression: `dict_global_nominal_receiver_native.spl` checks a global
registry lookup through another function, present/missing membership, local
dictionary lookup and a nonzero field index. The unit regression exercises the
real dictionary read hook with erased storage, retained Dict metadata and a
canonical class owner. These are targeted candidates, not a blanket claim that
all U0002 method failures are resolved.
