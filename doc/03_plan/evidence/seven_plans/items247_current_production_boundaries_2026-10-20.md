# Items 2, 4 and 7: current source boundaries

Independent read-only review plus root source checks. These are source findings, not runtime/host qualification. Candidate source: e4049c1437b; fetched base: d9e177de79a. Preserve the entire selected scope.

# REQ-004 independent production-gap review

Read-only review by /root/review_layout_owner_overlap; no execution claims.

Existing production owners implement retained per-kind high-water allocation,
forward/reverse aliases, tombstones, snapshot encode/decode, and atomic paged
updates. db_paged_txn combines row/tombstone, alias, reverse index, high-water,
Accepted and ActorCounter before sealing one manifest; settlement projects that
into one Git candidate and signed receipt. Accepted batches are co-persisted in
MaterializedState rather than fields of IdentityMap itself. Meaningful existing
unit/paged-settlement tests must be reused; umbrella placeholders do not prove
these owners absent.

The reviewed ordinary DbOperation and allocation/paged transaction/settlement
paths do not create MergedInto/SplitInto checkpoint disposition records.
Checkpoint codecs, validation and resolution already understand these records,
but that alone does not establish atomic creation of merge/split transitions
alongside allocation, aliases and acceptance. This remains a requirement gap
until an admitted writer/composition contract is identified or implemented.

A concrete durable-nonreuse acceptance extension can use the real paged Git
settlement fixture for create -> signed tombstone -> cold reopen -> new create,
reading actual alias, reverse index, high-water, Accepted and row pages. Test
both accepted batches, retained old aliases, tombstone and next sequence, plus
independent kinds. This slice must not be represented as full REQ-004 because
merge/split transitions remain outside it. Tests are currently UNRUN.

Cycle-5 candidate source remains frozen; this report is preparation only.


# Current item-4 production boundaries

Independent read-only audit of frozen e4049c1437b; no tests or mutations.

PR4014 is an ancestor of the candidate base and reports native internal fullCLI
ELF linking in79 seconds at approximately21GB. Indexed symbols and flat linker
data supersede the old blanket fullCLI input OOM claim. This is upstream
limited evidence, not whole-feature or current-candidate qualification.

RV64 static ELF has real driver, paired/arithmetic/GOT/ULEB128 relocations,
archive extraction, attributes and local-exec TLS owners. Alignment padding is
rewritten and tables reparsed. RELAX-marked CALL pairs are tested by preserving
full-size instructions, not iterative CALL/JAL/compressed relaxation. That
instruction relaxation remains missing. RV64 non-static-ET_EXEC modes are
explicitly rejected by elf_static_link.spl; dynamic/PIE PLT/GOT/TLS composition
is missing positive implementation.

ELF32 inspection and context-free relocation helpers exist; RV32 image linking
is explicitly unsupported by elf_static_machine. arm32_raw_link.spl separately
exists, so no blanket claim of absent ELF32-related code is justified.

PE AMD64/ARM64 has COFF archives, COMDAT/common/weak resolution, relocations,
imports/exports/base relocations and PE output. TLS attachment exists and
rejects data without _tls_used. Format-byte tests do not establish Windows
loader execution, application/exception/TLS behavior or all host contracts.

Mach-O hosted linking, provider/TBD closure, eager dyld fixups and embedded
signing exist. Local TLS initialization and unwind tables explicitly fail;
fat/shared-cache inputs and unsupported policy/flags have rejection contracts.
Those refusals are not positive support. Darwin execution is separate evidence.

Retain existing positive specs and negative controls. RV64 relaxation/dynamic
and RV32 driver completion need actual source work; changing refusal tests to
success assertions would not implement them. No completeness percentage or
all-host PASS follows from this audit. Candidate remains frozen and unverified.


# Current item-7 implementation and remaining integration

Read-only independent audit with root source review. No runtime PASS claimed.

Implemented source owners include typed unary extraction before monomorphization,
guarded Original/Linear/Hash/Ordered selection, a narrow MIR consumer for small
literal i64 map membership, typed and attributed CLI explanation paths, and
simple-collection-native-receipt-v1 artifact binding. Native publication calls
the receipt owner on normal and cache-backed paths and orchestration validates
receipts during reuse. The sidecar binds source, MIR, capsule, object, report
and output digests; it explicitly does not prove instruction survival or runtime
semantics. Older prose claiming no artifact receipt exists is stale.

The typed acceptance file has TWO distinct scenarios. The literal differential
scenario can gain validation of the existing sidecar plus tampered output,
request and report rejection. The attributed exact-site profile scenario still
requires workload/profile epoch -> selected typed storage -> native artifact.
Current receipt plumbing does not establish that join. Retain its explicit
MissingEvidence failure; replacing it with literal receipt assertions would
weaken the selected requirement and is not authorized by this audit.

Runtime-attributed explanation reports typed_mir=unconnected. Broad logical
join/group/distinct enumeration is not physical lowering; the inspected actual
consumer is narrow literal map membership. Full supported generic set/map/key/
operation scope and nested/hash/merge admission remain unproved or unconnected.
Stage4/native differential/guard execution is missing evidence independently of
these source integration gaps. Existing source should be reused, not recreated.

Sources: src/compiler/35.semantics/perf/collection_plan_extractor.spl;
collection_plan_selection.spl and collection_literal_membership.spl owners;
src/app/optimize/main.spl; src/compiler/80.driver/driver_collection_native_receipt.spl
and driver_aot_native_output.spl; test/03_system/app/compiler/feature/
profile_switchable_typed_plan_acceptance_spec.spl and guard acceptance.

Candidate e4049c1437b remains frozen through final authorized compiler cycle6.
