<!-- codex-research -->
# SOSIX runtime unification: nonfunctional requirement options

**Status:** awaiting user selection, 2026-09-26. The dated proposal names performance and release evidence, but its cited 2026-09-05 baseline/performance files are absent from current committed `main`. These options choose how numeric budgets become release gates; all retain the same safety and profile obligations.

## N1: performance budget admission

| Choice | Gate | Pros | Cons | Effort |
|---|---|---|---|---|
| **A. Measured profile budgets (recommended)** | First capture reproducible direct-call, hosted ring, SimpleOS guest and named-device baselines on admitted toolchains. Then commit numeric p50/p95/p99 latency, throughput, cold/warm startup, CPU, allocation, RSS and retirement-delay budgets per release row before implementation is promoted. | Avoids invented thresholds; isolates host/device variance and makes regression claims reproducible. | Numeric gates cannot be finalized until the baseline runs; requires maintained fixtures and hardware access. | Medium for baseline harness (about 8–16 files), then ongoing per-profile measurements. |
| **B. Fixed budgets before baseline** | Set numeric ceilings now for the same metrics, then test each named profile against them. | Gives immediate targets and a simple pass/fail rule. | Without current measured fixtures, thresholds risk being arbitrary or impossible on a qualified host; changing them requires a requirement revision. | Small to specify, large to calibrate later; about 4–8 initial files plus rework risk. |

## Common mandatory NFR gates for either choice

- **Safety:** zero observed use-after-retirement, duplicate completion, stale-generation acceptance, unauthorized capability success, or lost cancellation/control progress in adversarial test suites. A passing suite proves only its tested profiles and interleavings.
- **Bounds:** record and enforce queue, registered-buffer, pinned-byte, task-frame, mailbox and reset budgets per profile. The static/pool profile must show zero hidden hot-path heap growth under its admitted workload.
- **Direct alias:** inspect generated object/import tables for the promised libc symbol and absence of an `rt_*` forwarding hop; compare with a same-build baseline, not wall time alone.
- **Provider evidence:** each native host, SimpleOS QEMU target, physical board, rendering backend and GPU transport has its own receipt. Missing rows remain unqualified. A proxy GPU path never substitutes for direct-device authority/reset proof.
- **Operation metrics:** expose physical retirement lag separately from logical cancellation/timeout latency; include queue occupancy, wake/kick count, batching, CPU time and staging bytes.
- **Release gate:** no SimpleOS release claim until the pure-Simple build, linked strong handler/registry installation, live guest serial path, and required hardware rows have admitted evidence.

**Selection needed:** one N1 choice. Record concrete budgets and fixtures in `doc/02_requirements/nfr/sosix_runtime_unification.md` after the choice; delete this options file only after final requirements are accepted.
