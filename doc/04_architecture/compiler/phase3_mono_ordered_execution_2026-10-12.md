# Ordered archive mono execution

`hir_mono_archive_execution_v1` is the actual root/FIFO orchestration consumer.
It takes the sealed compact registration owner and the exact admitted names,
paths and order. Creation rechecks full coverage, the initial unrewritten state,
current repository authority, feature policy and immutable ascending root schedule
inside its own scope. Only the schedule digest escapes that verification scope.
The resident execution owner holds declaration facts, root IDs, artifact
publication descriptors, text diagnostics and scalar statistics; no full module
or function body is retained in the owner.

`mono_archive_execute_next_root_v1` selects the next module/root in admitted
module order and ascending SymbolId order. It invokes the existing actual complete
archived-function rewrite and publication application, then records the promoted
descriptor and exactly its diagnostic/warning/statistic delta. Empty-root modules
remain in the schedule and are crossed without changing the input inventory.

`mono_archive_execute_next_specialization_v1` refuses until every root has passed
that barrier, then invokes the existing real FIFO body consumer and publication
application. Newly requested cross-module templates extend the same FIFO. Existing
recursive-specialization deduplication, canonical signature/type substitution,
depth limits, defining-module ownership, mangling/collision checks and exactly-once
diagnostic policy remain in the shared actual consumer. No alternate allocator or
projected empty provider graph is introduced.

Each operation rechecks repository, feature policy, immutable root schedule and
the expected state epoch inside an owned scope. Metadata mutation happens after
the actual consumer has closed and applied its publication. Diagnostic text and
all three dynamic statistics are added once, in actual root/FIFO order; initial
generic function/struct/class counts come from actual ordered registration.

`mono_archive_execution_complete_v1` requires root coverage with no extra rows,
FIFO cursor equal to queue length, exact emitted coverage and specialization
descriptors matching every queue entry's module/name/SymbolId/body digest. This
is an execution coverage check, not admission of final assembled HIR or proof
that every stored artifact remains readable. Final module assembly must load and
validate every selected complete record, preserve symbol rows and final counter,
apply only the exact existing consumed-template pruning policy, and run all
post-mono validators before the final repository can admit MIR consumers.

The native fixture adds ten controls for unsealed or reordered creation, nested
leases, FIFO-before-root refusal, actual retained root/body parity, repeated root
or FIFO completion without repeated diagnostics, full FIFO/body/diagnostic/
warning/statistic parity, missing root coverage and changed epochs. The launcher
requires 66 checks. Native compilation/execution remain pending root serialization.
Static ownership/source guards are not native evidence. Production activation,
original promoted-body reclamation and full CLI RSS improvement are not claimed.

Dependencies are the compact registration producer/order gate, complete function
records/shared byte owner, real transient state query and the selected-provider
input key (`f7c60c79a8dc8187121c4f6357559c75e218eba1`) plus repository selection
binding (`232164581470b4ab94bb5add066164b59017f63c`). The private historical
branch does not contain the entire latest driver authority chain; it must be
integrated in dependency order before an admitted producer can execute this fixture.

Independent static review found that recomputing a schedule digest at execution
creation could accept root symbols removed after registration sealing. Registration
now records a promoted complete schedule digest after every validated actual body
publication. Capture/publication and seal compare current module/SymbolId rows to
that proof. Seal preserves the digest; execution creation compares to the preserved
sealed digest, not merely a new hash of mutable rows. Preflight continues checking
the same digest after creation. Three actual native controls remove root IDs before
seal, after seal and after execution creation, requiring refusal with unchanged
phase state and no FIFO creation. Combined with cross-module provider consistency
controls, the mono launcher requires 71 checks. All remain unexecuted pending the
root-owned native slot.
