# SCV cost instrumentation (review pending)

This patch measures existing source admission work. It changes no source
selection, facet, receipt, cache identity, publication, alias or rejection rule.
The two-second goal remains **unmet**. Four tiny native diagnostic rows passed
under the bootstrap Rust seed and core-C runtime. The reviewed instrumentation
has since been compiled into the next full producer, and its default Hello
compiled and ran successfully. Full Phase 3 and negative-oracle qualification
remain pending. The patch remains unmerged.

The actual 145-fixture cold admission published 42,796 inventory rows
(16,409,927 bytes) after 273.24 seconds, started snapshot staging 2.20 seconds
later, and materialized 14,869 selected sources in 172.43 seconds. Total time
from refresh-lock creation to snapshot receipt was 447.96 seconds. Evidence:
`C:/dev/simple-llvm-flags-corec-fixture-storage-20261025/evidence/scv-cold-cost-observation.sdn`.
Actual Fable 5.1 review is retained at
`C:/dev/simple-scv-fable-review-20261024/cold-live-review.txt`. It rejected a
merged existence/read operation as the first patch and conditionally approved
instrumentation. Its absent/error, race, physical-alias and tamper concerns
remain requirements, not waived checks.

## Scope

Only a valid existing `SIMPLE_INVENTORY_TRACE_ATTEMPT` token creates an
invocation-owned `ScvCompileCostV1`. Disabled invocations never query its clock.
The clock is `std.nogc_sync_mut.sffi.time.time_monotonic_ns`, whose
`rt_time_monotonic_ns` is an actual runtime export; `rt_time_ms` and
`rt_time_now` from the unresolved-stub list are not used.
Negative start/end samples and backwards intervals contribute zero duration;
the operation count and observed successful bytes are still recorded. An
unavailable clock interval is ignored, never interpreted as process uptime.

Direct Git file-event reduction counts existence calls, checked reads and bytes
returned by successful reads (not unobservable partial bytes from failed reads),
successful/deletion events, and the actual facet SHA256 calls. Event wall time
includes canonicalization and hashing; hash wall is a nested subset. Alias
expansion, filesystem journal decoding and library-internal hash calls are not
misrepresented as measured direct file events. The inventory total includes
the whole existing refresh, including lock wait and those other operations.

Snapshot materialization counts attempted full and reuse operations. Copy time
includes chunk publication and destination write/copy (including their existing
internal checks); explicit source, chunk, destination and drift verification
have a separate bucket. These buckets overlap and must not be added as if they
were disjoint. Snapshot total includes its unchanged owner checks and receipt
publication. Final source-authority validation remains unchanged and outside
the snapshot-acquisition bucket.

The carrier is allocated before scratch scopes. Inside a scope, diagnostics
only call the nonallocating clock and update scalar fields; no path, content,
formatting or log record is retained by the carrier. Core facet hashing accepts
an optional carrier so actual deduplicated hash calls can be counted, rather
than estimating from digest equality.

Existing historical inventory trace records retain their behavior. Exactly one
additional `phase=cost` aggregate is emitted through that trace owner after
refresh unlock and snapshot acquisition/validation, including failed acquisition
results. Failed unlock suppresses it. Nothing is logged per file or written to
SCV inventory paths by instrumentation. The record carries no authority.

Existing entrypoints and helpers retain their exact argument signatures through
old-arity wrappers forwarding a nil carrier. Instrumented callers explicitly use
new `*_cost_v1` symbols. `CompilerInventoryTraceV1` retains its original fields;
the separate cost carrier is passed explicitly, so diagnostics do not require
blanket cached-native-caller invalidation or change the existing trace layout.

## Required review and validation

### Measured full-source invocation with the instrumentation

The c635 Phase 3 invocation emitted its actual aggregate before frontend build
work at
`C:/dev/simple-phase3-c635-storage-20261025/phase3/.build.log.tmp.36860`.
The exact line and timing receipt are frozen separately at
`C:/dev/simple-scv-measured-io-review-20261025/actual-cost-line.txt` and
`C:/dev/simple-scv-measured-io-review-20261025/timing-receipt.sdn`.
Its inventory total is 217.0206669 seconds and snapshot total 219.2485282 seconds,
436.2691951 seconds combined. The two-second goal remains unmet.

| Measured bucket | Calls | Seconds |
|---|---:|---:|
| Direct file existence | 42,811 | 2.2722196 |
| Checked inventory read | 42,811 | 187.3925877 |
| Event reduction | 42,811 | 16.5924507 |
| Facet hash | 199,990 | 3.9391721 |
| Snapshot materialization | 17,360 | 216.4006080 |
| Chunk publication/destination copy or write | 34,720 | 147.9561401 |
| Explicit verification | 52,080 | 65.3718626 |

Successful inventory reads returned 301,440,540 bytes. These are nested buckets:
event time includes hashing, copy includes internal chunk verification, and
materialization includes copy and explicit verification. Do not add them as
disjoint wall time or treat the counters as all host I/O. The cost line itself
does not break copy time into write/open/readback components.

This is one observed invocation with different input and materialization counts
from the earlier 447.96-second observation. It is not a comparable before/after
speedup or a tracing-overhead measurement. The producer and ongoing Phase 3
remain provisional and unqualified; all existing failure and physical-validation
requirements remain. No live source or cache was changed to obtain this record.

### Later cold measurement and bounded warm-path audit

Source `60304aa7e52dd069937a3a9d764a8edd59c38b97` with a0ca recorded
299.1433388 seconds inventory plus 213.2329141 seconds snapshot, totaling
512.3762529 seconds. The raw aggregate is retained at
`C:/dev/simple-phase3-a0ca-storage-20261025/evidence/scv-cost-handoff-observed.sdn`.
Counts were 42,813 reads / 301,454,503 bytes, 200,000 facet hashes,
17,360 materializations, 34,720 copy/write operations and 52,080 verifications.
Subbuckets overlap; this is not a controlled comparison with the prior
436.2691951-second measurement and establishes no speed or overhead claim.

The read-only audit at
`C:/dev/simple-phase3-a0ca-storage-20261025/evidence/warm-scv-memory-handoff.md`
has SHA256 `5f2118e273d7efcd3cb62a13fb0cea341e8b9854c8c0b12905a702f22f99fe1d`
and pins its exact source files. `COLD_INIT=0` may reuse an exact valid snapshot
before materialization (`compile_snapshot.spl:696–704`), while alias enumeration
and fresh child-file reads remain (`inventory_aliases.spl:65–136`, reads
121–125). Inventory read/decode repeats at `inventory_events.spl:706–709`,
`compile_snapshot.spl:189–192` and `source_authority.spl:97–105`. A warm token
alone therefore promises neither unchanged generation nor two-second admission.

Observed parent RSS reached about 2.584 GB during child execution; without a
heap-live counter it cannot identify recoverable allocations. The guarded full
attempt stopped at 5,864,952 KiB against 5,859,375 KiB and became quiescent.
No warm retry or source/cache change accompanied this audit. Preserve the
failure and all source-validation oracles; no full Phase 3 qualification follows.

### Latest f825 cold measurement

The f825 aggregate recorded inventory 302.6244231 seconds plus snapshot
213.7444553 seconds, totaling 516.3688784 seconds. Checked read time was
270.5311948 seconds, copy/write 144.3432443 seconds and verification
63.8113419 seconds. These are overlapping buckets, not disjoint costs or a
controlled comparison with earlier runs. Exact retained aggregate:
`C:/dev/simple-phase3-f825-storage-20261025/evidence/scv-cost-handoff-observed.sdn`,
SHA256 `f5bb703927597ce76027baa10a02bb65ba770f868a0ce979012b76354e933963`.

Full source inventory CURRENT generation 1 had digest
`3806b102976648efcb79576c753758547b6f6bc069e1911550f8be6d0ebaaea3`;
its retained record is
`C:/dev/simple-phase3-f825-storage-20261025/evidence/issued-CURRENT-at-handoff`.
This is distinct from the 17,360-row selected compile snapshot revision
`scv-revision-v1-dd1f62eeb45e553430b00804ee9227b9368bd67267b2f2a54e6dc263272a0a6d`
and its inventory digest
`ad6f04ab428824106aa40b94a001fbada569af625c4b3a7debe83b37da10a7a3`.
The exact snapshot receipt path is recorded in the companion cold-admission bug.

The run terminated at the resource guard (outer exit 88, peak 5,882,244 KiB,
cap 5,859,375 KiB, quiescent), after 353 HIR completions / 5,543 explicit
functions, zero MIR/native phase rows and zero cached objects. Terminal receipt:
`C:/dev/simple-phase3-f825-storage-20261025/evidence/terminal-result.sdn`,
SHA256 `a601243fcec8a5a474e653c759df4de1d219da1c0b4151f0ee55930a27aa1c91`.
No executable/build receipt or full Phase 3 qualification follows. Required
verification and the two-second goal remain open; no green check was rerun.

### Retained native evidence

The later full producer is SHA256
`c63563672c95353d5475814ec0bc7241ca51b59c2e16646902c6f3a7a977873a`,
with 1,501 fresh units, zero reused and zero failed. Its default Hello evidence
is `C:/dev/simple-gnu-ready-hello-20261025/evidence/hello-result.sdn`;
the generated Hello SHA256 is
`6c1d66fd1dd21a3b56bebbbe0c1c781aa8b39508543edf4aa707f43f434e7cbe`.
Native DWORD 0, exact combined output and quiescent cleanup passed. That producer
still has 101 generated stubs and no formal admission. Ongoing Phase 3 is not
qualification, and no general runtime or two-second claim follows.

The real native fixture `test/fixtures/bootstrap/scv_cost_native/main.spl`
passed four rows on 2026-10-25. Frozen inputs, canonical argv, captured logs,
native receipts and summary are under
`C:/dev/simple-scv-native-parity-diagnostic2-storage-20261025/`.
The accepted narrow summary is `evidence/summary.sdn`, SHA256
`d7b4edfedfaabfe681ddbcf9fd3b16235c78077ce1a4e8acd453c41aa20915b7`.

The immutable bootstrap seed was SHA256
`5a6a8bec8c8c205b2c4507768acf553b3ef6027018706357350394af09f81622`.
It produced diagnostic program SHA256
`7e807f86cc9501e8230a4dd710263ae30aef2166283bde7c02c96c3bd3acf9f9`
(2,999,296 bytes), using one fresh unit and 150 cached units in 5.3 seconds.
The build used 24 workers, a 5,859,375 KiB cap and peaked at 1,479,568 KiB.
All four native rows exited DWORD 0, quiescent, with no cleanup or job remnants.

Real scratch helpers retained two events and the carrier through later scope
teardowns; timed/untimed event fields and encoded inventory bytes matched.
Counters recorded two reads, two events, six hashes and 78 UTF-8 bytes.
Externally captured bytes contained exactly one aggregate after the unlock
marker despite repeated emit, invalid-token and nil-carrier calls. The twin
source-authority rows matched inventory digest, source manifest digest, count
and generation. Enabled tracing emitted one aggregate and one of each historical
phase 1–4; disabled tracing emitted no aggregate. Real enabled monotonic
inventory/snapshot intervals were 223,068,000 / 53,668,300 ns. These tiny values
are not realistic-fixture performance or tracing-overhead evidence.

The executable remains unadmitted: its core-C link generated 13 unresolved broad
time-facade stubs, retained in `build/work.log`. `rt_time_monotonic_ns` is not
among them. This PASS does not qualify those providers, native-all composition,
the Rust runtime lane, or normal self-hosted tooling. The first attempt failed
after 151 successful unit compilations because the private sparse checkout
omitted `src/runtime/platform/platform.h`; its receipts and objects remain at
`C:/dev/simple-scv-native-parity-storage-20261025/`. A separately approved
platform-only readiness repair passed 29 actual clang dependency preflights
covering 64 files before the successful cache-preserving diagnostic.

The authored `scv_compile_cost_spec.spl` checks event/inventory byte parity,
deduplicated hash-call count, deletion behavior, disabled/invalid token gates,
lock-held suppression and scalar accumulation. It remains unexecuted.

Before full integration, measure tracing overhead in both wall and peak RSS on
a representative fixture with identical inventory bytes/digest and source
outcome. Match counts to the filtered
Git event stream, including deletions and failed reads; do not equate them with
all runtime I/O. Retain the existing unreadable/missing/race, physical-alias,
tamper, commit-advance and malformed-publication negative oracles. No before/after
speedup is claimed until comparable measurements exist.

The bounded native carrier-survival/cardinality plan is
`scv_cost_native_parity_fixture_2026_10_25.md`; its actual four-row execution is
recorded above. The separate authored unit spec remains unexecuted.
