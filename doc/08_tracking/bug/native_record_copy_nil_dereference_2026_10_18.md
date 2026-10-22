# Native value-record copy dereferences absent payloads

## Evidence

The admitted pure-Simple compiler d85dd53b7a1d5a3438d06c9856a3b252c02122f784411a9d9c330b2877dab708
built the typed dictionary pair nil control successfully. Its executable
5565d5f0b372d94cbeb7086989439e608dc1c1aeb98a7e35480c105785335469
then exited with SIGSEGV before the refusal marker. The bounded cycle had no
OOM; source/runtime pins remained unchanged and its execution scope drained.
Evidence: `struct-key-paired-nil-control-d85-20261018` under the external
`phase3-whole-tests-evidence-20261013` packet.

Disassembly preserves tuple slot words, then the typed record binding loads
through the absent key/value before the body can evaluate `.?`. The common
`copy_struct_value_recursive` owner reads fields unconditionally at its entry.
Its old nested-record guard checks native zero only, excluding runtime nil.
This is a native value-copy defect; weakening codec required-entry checks
would neither preserve data nor prevent the dereference.

## Repair and scope

Guard the recursive copy owner before its first field load. Obtain runtime nil
through ordinary `HirExprKind.NilLit` lowering, then compare record handle bits
against that value and a native zero constant. LLVM's existing bitcast owner
uses `ptrtoint`; Cranelift uses its existing pointer-width bitcast. This tests
address absence, not collection emptiness or scalar truthiness. `rt_is_present`
is intentionally unsuitable because native zero is a present scalar there.

The absent edge preserves the original bits in the typed merge slot. The
present edge performs the existing recursive copy and stores its fresh result.
Nested fields call the same guarded owner; their former zero-only wrapper is
removed. Local bindings, by-value parameters and native trait copy thunks all
share this owner. Struct identity, Result Err owner and generic field metadata
are attached to the returned merge local for all callers.

No heap record allocation or field dereference occurs on the absent edge.
There is an entry stack slot, two comparisons and a conditional branch for
each actual recursive record copy. Performance is **UNMEASURED**; no speed or
memory improvement is claimed. Fresh construction and class-reference copy
selection are unchanged. The open dictionary record-key hashing bug remains
separate.

## Validation

`record_copy_absence_spec.spl` constructs real MIR, executes its scalar guard
for native null, the compiler-generated nil word and a present address, checks
the selected block and original merge-slot payload, and checks direct-owner
metadata propagation. A frontend/MIR case covers parameter and nested copying.
`native_record_copy_absence.spl` checks absent typed bindings, parameters, tuple
destructuring, nested nil, and independence of non-nil record/nested copies.

All dynamic checks are **UNRUN** pending source review and a patched producer.
No fourth retry of the failing control or producer rebuild was performed.
Both native backends, the real MIR tests, and the original codec negative
criterion remain required. No codec or whole-suite PASS is claimed.
