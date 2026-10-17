# Declared tuple match subject ownership

C34's serializer dependency closure reported ambiguous `Int` and `Float` at
`src/compiler/50.mir/mir_instruction_graph.spl:388:11`, in
`mir_fold_binop(op, left: MirConstValue, right: MirConstValue)` matching
`(left, right)`. The terminal evidence and frozen producer/source identities
are recorded in `imported_positional_struct_owner.md`; the exact two diagnostics
are in that run's `normalized-mir-errors.json`.

HIR lowers tuple literals without an expression type. Match lowering formerly
recovered a subject type only from an expression annotation or a single variable
symbol, so a tuple of declared parameters lost its slot owners. The existing
`lower_match_pattern` tuple branch already assigns each child its exact declared
slot type, but could not run without a tuple subject type. General tuple-match
desugaring then emitted enum tests whose bare variant names remained ambiguous.

The new helper preserves existing expression/symbol annotations and recovers
an unannotated tuple literal only when every child has a concrete declared type.
It recursively handles nested tuple literals and retains exact symbol IDs per
slot. Unknown or non-concrete children leave the existing unresolved route
unchanged. The helper inspects existing HIR; it does not lower, evaluate, clone
or reorder source expressions, so the existing once-only scrutinee evaluation
and short-circuit match tests remain unchanged. It introduces no variant-name
search, HIR fields, codec changes or global owner fallback.

`test/fixtures/compiler/declared_tuple_match_owner/` uses imported same-basename
enums whose `Int`/`Float` variants have different payload types and declaration
orders. Assertions cover same-owner pairs, heterogeneous pairs, nested tuples
and mismatched-variant fallthrough. The authored SSpec includes real parsed
HIR/MIR lowering, unknown-slot rejection and annotation preservation.

Native qualification is pending a coordinated changed-source producer. No
compiler build or repeated C34 run was launched. Next gate: ARM exit zero with
`declared_tuple_match_owner: PASS`, then explicit LLVM 18 RISC-V object/ELF
machine 243 qualification. Keep unknown-owner negative behavior and run the
existing serializer fixture unchanged. The no-span missing-runtime-identity
and multiple-wildcard diagnostics remain unattributed; this patch does not
claim to repair them or the other serializer MIR groups.
