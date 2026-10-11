# Generic nominal transport candidate

Status: unqualified source candidate, 2026-10-11. User selected full generic
correctness, Phase 3 compilation/tests, logic/memory review, and release sharing.

`nominal_type_relocation.spl` transports batches of HIR types between symbol
tables by canonical declaration owner/name. It validates the complete batch
before allocation, rejects stale target bindings and conflicting source kinds,
preserves all nested symbol-bearing type forms and non-symbol metadata, and
allocates fresh rows without lexical shadowing. Identical declarations already
in a shared table are reused without changing the source table. Callers must
reserve symbol counters against live specialization IDs and retain the returned
table. Failed results contain no usable types.

This helper is prerequisite work for H-XMOD and H-RET32: actual generic type
arguments must move caller-to-template before specializing; stamped signatures
must move template-to-caller before MIR reads them. Wiring and removal of unsafe
MIR name heuristics are pending. Merely adding this helper fixes no call site.

Source review found and corrected three issues before publication: accepting
same-kind stale qualified target entries; lexical allocator reuse; and source
alias kind conflicts within a batch. Independent rereview found zero P0/P1 under
the documented table/counter preconditions. Focused specs include those failures,
same-table source preservation, imported identity reuse, owner normalization,
absent IDs, lexical decoys and nested function/array metadata.

Execution evidence: UNRUN. No admitted self-hosted test runtime is available to
this lane yet. No branch coverage, Phase 3, native correctness, memory safety or
release qualification PASS is claimed. Required follow-up is unit execution,
caller/provider integration, native cross-module generic return fixtures with
colliding IDs and names, RV32 ABI shape checks, and compiler/core/MCP smoke.
