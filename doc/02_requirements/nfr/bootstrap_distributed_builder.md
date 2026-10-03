# Bootstrap distributed builder nonfunctional requirements

Date: 2026-09-30. Bounds are implementation safeguards; runtime performance has
not yet been qualified.

- NFR-BBM-001: protocol payload at most 16 MiB, 262,144 scalar fields, decoded
  scalar at most 65,536 characters, 4,096 tasks, 64 configured hosts, 1,024
  argv values per task, 4,096 declared inputs/outputs/dependencies per task.
  Reject excess before scheduling. Test malformed and oversized records.
- NFR-BBM-002: host slots bound observed live workers; replacement requires
  confirmed reap. No extra RSS cap is introduced into the user's bootstrap.
  Record requested slots and observed concurrent processes separately.
- NFR-BBM-003: retries at most three attempts per task. Preserve stable cache
  roots and completed artifacts. Measure actual warm task reuse, compilation
  latency, maximum RSS, and cache invalidation using the same source/toolchain.
- NFR-BBM-004: parent alone commits canonical state and compiler cache receipts.
  No worker can publish another attempt's outputs or mutate shared manifests.
- NFR-BBM-005: cache counters are observed nonnegative values or `-1` (unknown).
  Retained cache files and task-result reuse are not compiler cache-hit evidence.
- NFR-BBM-006: avoid opening compiler/MIR implementation closures in the manager
  startup path. Shared wire contracts live under `src/lib/common/build_manager`.
  Record cold/warm native startup time and max RSS before qualification; no
  unmeasured startup or distributed speedup target is claimed met.
