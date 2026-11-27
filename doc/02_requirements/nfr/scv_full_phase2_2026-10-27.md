# Full SCV and phase 2 compiler: quality requirements

Date: 2026-10-27. Status: inherited quality requirements; numerical performance budgets not yet selected.

| ID | Required property | Verification mechanism |
|---|---|---|
| NFR-001 | Acknowledged retained work and required identity/reconstruction closure survive failure | Crash-at-boundary and independent parser-free restore campaigns; AT-M01/M04/M05 |
| NFR-002 | Incomplete data, watcher coverage, validation, provider availability or references never imply success | Negative controls and explicit unknown/unavailable results; AT-P01/P03/P06, SCV-CACHE-06/09/24 |
| NFR-003 | Equivalent deterministic inputs produce equivalent plans across scheduling/providers | AT-P05, hash vectors and scalar/SIMD differential execution; no acceptance from a timeout-dependent winner |
| NFR-004 | Namespace isolation, old-policy authorization and one protected publication authority | Capability denial, stale authorization, fencing and upstream races; AT-C04, AT-P02/P06, AT-G02/G06 |
| NFR-005 | CPU/RSS/I/O/metadata work is budgeted; no save/build feedback or nested scheduler explosion | AT-E06–E08, AT-R01, bounded queue/scheduler/retention measurements |
| NFR-006 | Warm verified output does no compiler work; new relevant absence-breaking input cannot hit stale cache | SCV-CACHE-01/02/09/28 with actual task counters and independent semantic oracle |
| NFR-007 | Legacy histories, SHA-256 v1 signed payloads and package action V1–V4 retain original meaning | AT-H07, AT-M02/M03, SCV-CACHE-24; dual readers and shadow comparison |
| NFR-008 | Benchmark claims include total native/Git coexistence and metadata, not only payload compression | Master §24 metrics; pinned fixtures/environment and actual denominators |

Measure cold/warm p50/p95/p99 latency, snapshot barriers, changed-file verification, branch-switch cost, queue/lease time, compiler task counts, peak RSS, bytes/path, total retained bytes and recovery rate. Existing example debounce/memory/record-size values remain experiment settings, not guaranteed targets. No new timing/RSS/storage limit is accepted here.

Planning review PASS, if earned, applies to these documents alone. Runtime production status stays NOT RUN until the linked acceptance scenarios execute on the required implementations and platforms.
