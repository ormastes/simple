# Cold source inventory validation scratch retention

Status: candidate repair, qualification pending.

The Cranelift Phase 2 producer `33517e08dc520f7016ccc228a973f0b65de069b12aead83885168d6afb18a69d` exceeded the 5,859,375 KiB guard on two cold Phase 3 attempts. A hashing stack sample did not identify retained allocations.

New bounded probes in `/tmp/simple-inventory-memory-fix-evidence` show 44,942 per-file events completing with roughly 141 MiB RSS and successful file-scope promotion/end. An uninterrupted private-worktree probe later reached publication readback, then exhausted a 1 GiB virtual-memory diagnostic limit at roughly 959 MiB RSS in `rt_string_join -> compile_source_inventory_encode_v1 -> compile_source_inventory_decode_content_v1 -> publication_readback`. This diagnostic limit is not a changed bootstrap admission cap. A separate Git pack mapping warning from that virtual limit is retained.

One actual production entry validator call returned true and retained nine heap objects. Wrapping that same call in debugger-invoked native scope begin/end returned true with zero object growth. This establishes reclaimable validation scratch; it does not execute the compiled candidate or prove full resolution/performance.

The candidate bounds each entry's validation scratch through the existing stdlib transient provider. Only a successful scope owner ends it; nested callers retain their existing scope. Validation rules, canonical bytes and hashing stay unchanged. Begin-false can also signal inconsistent raw bookkeeping; no active-scope query exists, so the compatibility path cannot certify reclamation in that condition.

Native paired validation, unchanged negative contracts, nested ownership, complete cold publication RSS and elapsed behavior remain mandatory. The current producer's narrow native diagnostic hit a 950,000 KiB codegen cap; a changed low-memory diagnostic failed all 11 capsules with `capsule-identity-mismatch`. Those are retained failures, not test passes.

## Targeted native evidence

Normal native baseline and candidate harnesses were compiled by the exact pure Cranelift producer above, with separate sources/caches and the unchanged managed `core-c-bootstrap` runtime authority. The bounded 2 GiB compile reservation was diagnostic; neither compile meets the 1 GB ordinary compile target (about 1.67 GiB peak). The diagnostic does not increase the Phase 3 admission cap.

Both 50,000-call harnesses completed with uppercase/short-digest rejection, caller-owned scope survival and exact canonical wire assertions. Baseline retained 950,009 objects, ran in 0.40 s and peaked at 83,892 KiB; candidate retained only nine initialization objects, ran in 0.33 s and peaked at 4,960 KiB.

After one warm call, the independent batched workload measured:

| Calls | Baseline object growth / elapsed | Candidate object growth / elapsed |
|---|---|---|
| 25,000 | 475,000 / 193,158,756 ns | 0 / 175,180,304 ns |
| 50,000 | 950,000 / 454,916,146 ns | 0 / 366,480,806 ns |

Whole batched process peaks were 116,648 KiB baseline and 6,484 KiB candidate. These finite samples demonstrate eliminated steady-state validation retention and no observed elapsed regression; they are not statistical or whole-bootstrap performance admission. The strict native fixture warms provider metadata before measuring zero growth.

Profiling attempts using runtime argv failed before work, and `host.current_time_ms` was absent from the actual core archive. Failed artifacts remain in the evidence directory. The successful workload uses the existing `sffi.time.time_monotonic_ns` provider; no clock/argv production change was made.

Full cold publication with a producer containing the candidate, the checked-in SSpec and native fixture, broader runtime checks and Phase 3/4 admission remain pending.

## Checked-in regressions

The immutable candidate commit `79c27b881a7a2863d99c3023ffa683f73e3548f2` was tested directly. Phase1 bootstrap-seed interpretation executed all four checked-in SSpec cases: four passed, zero failed/skipped/dropped, exit 0, peak 645,536 KiB. Receipt and test output: `/tmp/simple-inventory-memory-fix-evidence/phase1-spec/`.

The checked-in native fixture was separately compiled by exact pure Cranelift producer `33517e08dc520f7016ccc228a973f0b65de069b12aead83885168d6afb18a69d` and executed with guarded compile/run receipts. Exact stdout asserted `validations=50000`, `objects_delta=0`, and `negative_and_nested_and_canonical=pass`; stderr was empty and both processes exited 0. Evidence: `/tmp/simple-inventory-memory-fix-evidence/checked-native-fixture/`. This proves the checked-in retention and semantic regression assertions, not complete cold publication or Phase3/4 admission.
