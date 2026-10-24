# SCV immutable inventory reader retains decode scratch until parent exit

Status: source implementation and native fixture authored; native A/B UNRUN.

Observed whole-pipeline failures remain preserved: Phase3 RSS guard 88 after
353 HIR modules / 5543 functions; warm parent roughly 2 GiB while child grew.
Full CLI also hit its unchanged tree guard before frontend output. These facts
do not establish that the inventory reader accounts for all retained memory.

`compile_source_inventory_read_at_pointer_v1` authenticates an immutable blob,
splits rows and fields, validates entries, and re-encodes canonical bytes. Its
returned graph contains an optional full inventory; intermediate file text,
framing arrays, sorting/encoding and hash scratch need not escape. Warm refresh
and snapshot selection call it before per-file work, outside the existing
compact authority-validation scope.

The narrow wrapper preserves the public signature, original admission body,
keys and canonical bytes. It scopes only an unowned state0 call; active/paused
callers and refused begin use the unchanged helper. Promotion retains the full
ReadV1 graph before retiring scratch. Failure results are constructed after
retirement; failed pause/promote/end never returns the potentially retired
result. Failed end is not retried or represented as restored state.

Do not widen this to refresh, snapshot acquisition or all source acquisition:
file event and snapshot materialization helpers hard-fail nested begin. Their
per-file lifetime boundaries must remain independent.

Actual Fable5.1 plan first REVISE, follow-up APPROVE for source authoring only.
Code review requested first-reader cold initialization coverage and bounded
encoding work; both fixture changes are included. Code follow-up APPROVE is
conditional on the actual native gates. All four bounded reviews are retained.
Both reviews and raw model receipts are external evidence. Source checks show
split/substring copy text in C and Rust; short caches are persistent/shared.
Both promotion owners traverse registered raw structures, arrays and enum
payloads. Owner-mode raw promotion updates the same canonical ownership table
that scope retirement reads. Those source facts do not replace native proof.

The fixture authenticates captured bytes independently, decodes its reference
outside the new wrapper, compares every retained row field after allocation
churn, and checks reference formation only. Formation does not prove allocation
membership or liveness. Lifetime evidence is exact retained data after churn,
actual managed-heap reclamation, and paired OS memory observations.
A separate dynamic heap allocation/count decrease witnesses real reclamation
without dereferencing discarded allocations. A constant-zero provider cannot
pass that witness. Caller states0/1/2 and malformed pointer/header/row/traversal
alias/canonical payload rejections are exercised through the real reader.
Uninjectable runtime failure branches receive source review, not fabricated
native coverage. No snapshot-manifest or physical-alias authority is invented.

Representative corpus: genuine immutable generation1, 42,813 entries,
16,416,628 bytes, SHA256
`3806b102976648efcb79576c753758547b6f6bc069e1911550f8be6d0ebaaea3`.
It is copied into private canonical storage for reader diagnostics only;
this is not source-admission authority for a build.

Pending native gates: same fixture/input baseline and changed builds, actual
core-C link-provider custody, real lifetime/churn/ownership checks, OS-collected
RSS/commit with no worse peak and lower retained reader-workload memory. Any
core-C pass is specific to that provider and does not qualify Rust058 or a
bootstrap descendant. The fixture performs one canonical encode/hash after all reader iterations;
its independent reference graph and all-field comparisons are equal work in
baseline and changed profiles. A subsequent actual parent pre-child measurement is
required before claiming a whole-pipeline memory improvement. No cap increase,
forced cache keys, full Phase3 retry or native execution occurred in this task.


Final-cycle fixture correction, native attempt2 still UNRUN: the first baseline
build passed69modules(7cached/62fresh), native0/quiescent1. Its run deliberately
assert-aborted at ordinal8 in the unsupported struct-registry check. The new
reader wrapper was not present in that baseline; no deep-promotion conclusion
follows. Seed StructInit uses raw `rt_alloc`, whereas `rt_struct_receiver_valid`
checks the separate registry populated only by `rt_struct_alloc`. Core-C's own
encoder comment documents that raw AOT structs are not registered there.

The corrected fixture calls existing `rt_heap_ref_wellformed` as a defensive
formation probe only. Every field comparison and the independent canonical
hash remain mandatory. Churn now allocates five distinct64-byte digest strings
and real ReadV1/Inventory/Entry/Option/array shapes per iteration; all record
fields and digest prefix bytes affect an observable checksum. No known-freed
witness pointer is dereferenced. Predicted final counter remains3,767,706 for
42,813 rows; it is not an actual pass. Original source/manifests/native abort
evidence are frozen separately. This is the final feature cycle6; no further
source repair or native retry is authorized after its terminal result.
