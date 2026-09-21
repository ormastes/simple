# macOS SCV cold inventory scratch retention

Status: OPEN — source correction implemented; native correctness, memory, and
performance qualification remain blocked. Scope: `aarch64-apple-darwin` only.
Related: compiler TODO 319 and `stage3_macos_compile_peak_rss_2026-09-21.md`.

Cold admission reduced every source file to an event but did not reclaim its
canonicalization, hashing, and file-read scratch. Publication sorted and
searched the growing inventory for every create, making initial application
quadratic. Digest validation allocated one text value per hexadecimal byte.

The correction opens one transient scope per file, promotes only that event,
and ends the scope before appending to the retained array. Scope failures
propagate through Git event production. Unique creates into an empty inventory
validate and append once, then sort once with a bounded-memory heap sort.
Duplicate, delete, update, and invalid events retain the sequential path.
Already sorted inventories use a linear fast path. Digest validation reads
ASCII bytes. Public inventory APIs remain exposed through the original module;
pure records and reduction now live in `compile_source_inventory_core.spl`.

## macOS Phase 2 evidence

Compiler: admitted Astra Stage 2, SHA-256
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`.
Base checkout: `20245f731db`. Required integration predecessors include
`531f948d0fe` (transient ownership boundary) and the `80cc02571d4` lineage
(ASCII split and HIR ownership corrections).

Three focused native compile cycles used the bare positional pure-Simple
`native-build` route and its admitted runtime archive. These were diagnostic
single-process compiles; the required jobs=8 full compiler gate was not run.

| Cycle | Elapsed | Maximum RSS | Outcome |
|---|---:|---:|---|
| 1 | 12.22 s | 1,105,330,176 bytes | HIR rejected the existing `std.io` lock import |
| 2 | 8.45 s | 874,053,632 bytes | HIR passed; MIR lowering exited 139 |
| 3 | 5.67 s | 421,707,776 bytes | Smaller pure closure passed HIR; MIR rejected unsupported operations |

Cycle 1's lock import now names its actual `std.nogc_sync_mut.io.file_ops`
provider. Cycle 3 reports existing array `remove`, SHA core `get`, builder
`to_text`, binary inspector `bytes`, range-index, non-array iteration, and
inferred-enum lowering failures. It produced no executable. The final measured
compile peak is below 1 GB, but different closures and early failures mean
these rows are not before/after performance evidence for cold admission.

Logs remain under `build/native_probe/scv-inventory-memory/` in the isolated
worktree. The third run enabled `SIMPLE_NO_STUB_FALLBACK=1`.

## Remaining acceptance

### Follow-up MIR reproduction, 2026-09-21

At PR head `f2419dda909`, the same admitted Phase 2 producer reached MIR for
the 16-module fixture closure, then looped in `MirLowering.bind_local`.
A macOS process sample captured the insertion probe calling `rt_array_get`;
resident memory was 643,152 KiB at 41 seconds. The diagnostic was terminated.
The index was promoted correctly, but `reset_function_local_tracking` cleared
its authoritative key/value arrays without clearing `local_symbol_index_slots`.
Occupied buckets accumulated across functions until insertion had no empty
bucket. The reset now clears the index together with its arrays. The existing
reset assertion and a 32-function bucket-occupancy regression cover the defect.
Executable validation requires a producer rebuilt with this compiler correction.

This reproduction used `--threads 8` with the explicit diagnostic
`SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct`; it does not qualify the full
jobs=8 SCV coordinator. The normal coordinator correctly refused this new
worktree before compilation because its SCV journal had not been initialized.

The follow-up source correction keeps the inventory's closure on canonical
leaf owners: space-token splitting, crypto word operations, and UTF-8 byte
conversion were extracted unchanged from their broad modules. Original module
paths re-export the same APIs. SHA core reads now use indexed accesses within
the existing bounds, and hexadecimal output uses the established substring API
over the ASCII digit alphabet. Inventory deletion builds ordered survivors
because the Phase 2 MIR lowerer does not support array `remove(index)`.
No digest algorithm, canonicalization rule, or inventory schema changed.

The executable fixture additionally checks externally pinned empty/ASCII SHA
digests, UTF-8 byte conversion and pure-Simple digest fallback, scalar SHA block
processing, token trimming, ordered deletion, and deletion idempotence. These
new assertions are authored pending the refreshed Phase 2 producer. The
underlying broad-module `StringBuilder`, binary-inspection byte-method, and
general range/iteration/inferred-enum MIR limitations remain production compiler
blockers until their own native checks pass; shrinking this fixture's import
closure alone does not qualify those surfaces or canonical Stage 3.

`src/lib/common/text_bytes.spl` owns the raw `rt_text_to_bytes` and
`rt_bytes_to_text` boundary formerly owned by `string_core.spl`. It is listed
as a sanctioned runtime provider because these are runtime ABI primitives;
callers use its semantic wrappers and do not declare or call the ABI directly.

The native fixture authors 256 repeated event scopes with digest/lifetime
checks, nested-scope refusal, a 2,048-entry reversed batch, and duplicate
generation checks. Its `--baseline` mode retains unscoped per-file work for
a comparable elapsed-time/RSS measurement. Neither mode executed because no
binary was produced. SSpec cases are also authored but unexecuted.

Fix the Phase 2 MIR blockers, run the fixture and matching baseline, then
qualify a full jobs=8 cold admission and compiler build below 1,000,000,000
bytes without a meaningful elapsed-time regression. TODO 319 remains open.
The three-cycle cap was reached; no further compile attempts were made.

## Executable cross-resource regressions, 2026-09-21

Added `test/05_perf/scv/compile_source_inventory_resource_profile_spec.spl`
and its native `test/fixtures/scv_inventory_memory/profile.spl` workload.
They compare scoped/unscoped construction at 256/512 files and
batch/sequential reduction at 512/1,024 entries, with complete facet/encoded
digest equality, elapsed scaling, per-process peak RSS and growth comparisons,
and strict <1 GB native compile/runtime caps. The supporting shell collector
verifies the admitted producer/runtime hashes and fails closed on missing,
failed, or timed-out native evidence.

A new isolated-checkout diagnostic used admitted producer
`e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`.
After an initial package-index admission refusal, explicit cold initialization
reached HIR and monomorphization but crashed in MIR (exit 139), at 7.27 seconds
and 883,605,504 bytes maximum RSS. It reported malformed HIR types and qualified
name field-list collisions. The workload did not execute, and the producer
does not provide `test`; these new executable regressions remain unqualified.
See `doc/06_spec/05_perf/scv/compile_source_inventory_resource_profile_spec.md`
for thresholds, commands, and limitations. No full bootstrap was attempted.

Review follow-up: the resource SSpec now requires strict live-object-count
separation between scoped and unscoped construction, with a native unit
negative control for the original unscoped mutation. The collector now invokes
the canonical admission validator instead of accepting hashes alone. All five
fabricated-receipt negatives refuse before producer invocation. Full admission
of the previously selected producer currently fails the sanity version binding
(`1.0.1-beta.1` receipt versus `1.0.0-beta.14` checkout). Consequently the prior
MIR row remains diagnostic history, and no new native qualification is claimed.
