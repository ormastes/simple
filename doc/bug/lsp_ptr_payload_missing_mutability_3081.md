# LSP compiler crash from a missing Ptr payload argument (#3081)

See https://github.com/ormastes/simple/issues/3081 for exact core/binary identities.
The admitted e644 Phase2 compiler accepted `Ptr(type_)` in Result Err record
materialization, although Ptr declares `(pointee, mutable)`. Generated code
passed a single MirType as the enum payload; the verifier decoded an array,
received nil, and dereferenced address zero at recursive depth one. The core
identifies `virtual_source_read_registry_v1._stat_v1`, unnamed local 37.
This was not an OOM: recorded peak RSS was 1,030,700 KiB.

The caller repair supplies `false`, matching the immutable pointer used to
read/copy the payload. It changes neither provider-owner validation nor MIR
verification. A bounded audit of 43 owned-source Ptr constructor/pattern
occurrences found only this missing-argument occurrence.

`native_mir_ptr_payload/main.spl` runs real MIR verification for scalar,
nested and struct-owner pointers and requires MIRV-001 for an unresolved
pointee. `mir_ptr_missing_mutability/main.spl` is a known compile-negative
input for the separate enum-arity diagnostic gap (#3082: https://github.com/ormastes/simple/issues/3082); this patch does not fix
that compiler validation gap. Neither fixture has executed yet.

Next gates: review; build repaired producer; run the positive fixture and
negative compiler input; manually compile the actual virtual source registry
through HIR/MIR/ELF object; then retry LSP. Frozen a511 source and e644 binary
are preserved. No native build was run during offline diagnosis.
