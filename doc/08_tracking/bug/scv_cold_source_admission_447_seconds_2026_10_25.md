# SCV cold source admission takes 447.96 seconds

Status: OPEN. The requested two-second commit-base snapshot goal is unmet.
Instrumentation remains unmerged. Its reviewed bytes were integrated into full
producer `c63563672c95353d5475814ec0bc7241ca51b59c2e16646902c6f3a7a977873a`
(1,501 fresh units, zero failures), whose default Hello compiled and ran.
Evidence: `C:/dev/simple-gnu-ready-hello-20261025/evidence/hello-result.sdn`.
Full Phase 3 and mandatory self-hosted/core/MCP/negative-oracle gates remain
pending; the producer's 101 generated stubs and no-admission status are retained.

## Actual observation

The Windows 145-fixture run published 42,796 inventory rows (16,409,927 bytes).
Refresh-lock creation to CURRENT publication took 273.24 seconds. Snapshot
staging began 2.20 seconds later; materializing 14,869 selected source files took
172.43 seconds. Refresh-lock creation to snapshot receipt took 447.96 seconds.
Observation receipt:
`C:/dev/simple-llvm-flags-corec-fixture-storage-20261025/evidence/scv-cold-cost-observation.sdn`.
The independent existing Fable review is retained at
`C:/dev/simple-scv-fable-review-20261024/cold-live-review.txt`.
Repeated physical work is a hypothesis requiring bucket measurements; these
timestamps do not independently attribute every second to hashing or copying.

## Narrow diagnostic evidence

### Actual instrumented full-source cost

The later c635 invocation emitted 217.0206669 seconds for inventory and
219.2485282 seconds for snapshot, 436.2691951 seconds combined. Its 42,811
checked inventory reads returned 301,440,540 bytes and took 187.3925877 seconds;
42,811 existence probes took 2.2722196 seconds. Event reduction took
16.5924507 seconds, including 199,990 measured hash calls taking 3.9391721 seconds.
Snapshot materialization counted 17,360 operations and 216.4006080 seconds,
with 34,720 chunk-publication/destination copy-or-write operations taking
147.9561401 seconds and 52,080 explicit verification operations taking
65.3718626 seconds.

These buckets overlap: materialization contains copy/verification, event
contains hashing, and copy includes internal chunk verification. They do not
identify separate open/write/readback costs, and must not be added as disjoint
wall time. Retained exact line and timing receipt:
`C:/dev/simple-scv-measured-io-review-20261025/actual-cost-line.txt` and
`C:/dev/simple-scv-measured-io-review-20261025/timing-receipt.sdn`.
Original live log:
`C:/dev/simple-phase3-c635-storage-20261025/phase3/.build.log.tmp.36860`.

The source/materialization counts differ from the earlier 447.96-second run;
this is not a controlled speedup or overhead comparison. The two-second goal
remains OPEN, c635/ongoing Phase 3 remain provisional, and current source,
snapshot, failure and physical-validation policy is preserved.

### Small native contracts

The new instrumentation preserves 103 existing function signatures, using
16 old-arity nil-forwarding wrappers and explicit new diagnostic symbols.
All 43 relevant call sites match declared arities; the existing trace carrier
layout is unchanged. Negative/unavailable monotonic samples contribute zero
duration instead of uptime. No admission, alias, no-follow, race, source
selection or tamper rejection rule is weakened.

Four actual native rows passed with immutable bootstrap seed SHA256
`5a6a8bec8c8c205b2c4507768acf553b3ef6027018706357350394af09f81622`
and a fresh core-C target runtime: real event/carrier survival across transient
scope teardown, captured aggregate cardinality, disabled source authority, and
enabled twin source authority. Events and inventory bytes matched; captured
enabled output contained exactly one aggregate and historical phases 1–4;
disabled output contained no aggregate. Source inventory and manifest identities,
two-source membership count and generation matched. Actual nonzero monotonic
intervals were observed. Summary:
`C:/dev/simple-scv-native-parity-diagnostic2-storage-20261025/evidence/summary.sdn`,
SHA256 `d7b4edfedfaabfe681ddbcf9fd3b16235c78077ce1a4e8acd453c41aa20915b7`.

The successful build compiled one unit, reused 150 and linked in 5.3 seconds;
24 workers, peak 1,479,568 KiB, 5,859,375 KiB cap. All four rows had native DWORD
0, quiescence and no cleanup/remnants. Program SHA256:
`7e807f86cc9501e8230a4dd710263ae30aef2166283bde7c02c96c3bd3acf9f9`.
The first harness failure (missing sparse `platform/platform.h`) remains intact
at `C:/dev/simple-scv-native-parity-storage-20261025/`; no failed result was
relabelled. Its approved platform-only repair preflighted 29 real C dependencies
and pinned 64 files before retrying with the retained object cache.

The executable is a bootstrap/core-C diagnostic and remains unadmitted. Its
13 unresolved time-facade symbols are `rt_time_now_ms`,
`rt_time_now_seconds_f64`, `rt_timestamp_add_days`, `rt_timestamp_diff_days`,
`rt_timestamp_from_components`, `rt_timestamp_get_day`, `rt_timestamp_get_hour`,
`rt_timestamp_get_microsecond`, `rt_timestamp_get_minute`,
`rt_timestamp_get_month`, `rt_timestamp_get_second`, `rt_timestamp_get_year`,
and `rt_timestamp_now`. `rt_time_monotonic_ns` is not among them. No general
clock facade, native-all runtime or self-hosted tooling qualification follows.

## Remaining work

Complete qualification of the reviewed producer, preserving the existing unreadable,
missing, race, physical-alias, physical-tamper, commit-advance and malformed
publication negative oracles. Run representative tracing-overhead and bucket
measurements after integration; do not rerun the already-green tiny diagnostic.
The separate unit spec remains unexecuted. Small-fixture PASS does not establish
the requested realistic 42,796-source latency or broad failure-policy parity.

The unimplemented commit-base inventory plus dirty overlay and lazy verified
capture proposal is `doc/05_design/scv_commit_base_lazy_capture_proposal_2026_10_25.md`.
It requires architecture review, complete related read-sets and explicit
resolution of outside-closure invalid/unreadable/tampered-source compatibility;
no Git-status, mtime or physical-alias shortcut is admitted by this report.
