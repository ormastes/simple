# Diagnostic parallel executable batches

The opt-in `scripts/bootstrap/adaptive-executable-batch.py` preserves the reviewed
Windows diagnostic scheduler used to collect independent native compiler and link
failures. It is **not a production buildrunner default or release admission**.
The existing bootstrap scheduler contract remains the owner of parent admission;
this helper only schedules executable tasks inside one admitted group.

Run the helper beneath the canonical Windows CFEC collector with
`--root-exit-policy terminate-job`. The collector must contain the Python parent,
all child qualification processes, native compilers, linkers, and nested RSS
collectors. The parent reservation remains held until the collector reports whole
tree closure. A child exception without a quiescent receipt stops new admissions,
drains known active children, then exits so the parent collector can reap any
remaining descendants. Do not substitute a PID-only kill or release a reservation
because a log is quiet.

## CPU and memory contracts

One group reserves **20 jobs**, not 20 jobs per executable. Each task uses
`native-build --threads 1`, `SIMPLE_NATIVE_BUILD_THREADS=1`,
`SIMPLE_HIR_SHARDING=0`, and `SIMPLE_PARSE_SHARDING=0`. The last two switches prevent
nested frontend worker groups. The maximum executable concurrency is configurable
from 1 through 20. Other groups still participate in the shared aggregate budget
(for example three other 20-job groups plus this group under 80).

Start one task without a fabricated memory measurement. After each completed,
quiescent task, use its measured **whole process-tree RSS**, a configurable safety
factor, available Windows system commit, and reserved headroom to admit additional
tasks. Grow the concurrency ceiling by at most one per measurement. Outstanding
tasks remain conservatively budgeted even if their committed memory is already
included in system usage. Low available commit queues pending work; it never kills
running work or converts diagnostic memory pressure into a compiler failure.

RSS is not private commit and the estimate is not an enforced bound. Whole-task
RSS includes frontend/codegen/link work and must not be described as linker RSS.
No isolated linker-memory estimate or speedup is established by this helper.
Different entry closures can have substantially different peaks. Native linking
may internally be serial even while multiple executable tasks overlap.

## Packet interface

The helper takes `--packet PATH` and optional `--preflight`. Host paths, producer
bytes, source authority, cache locations, and 420-target inventories belong in
external immutable diagnostic packets, never this source file.

`config.json` requires these values (paths are supplied by the owner):

```json
{
  "aggregate_jobs": 20,
  "global_job_budget": 80,
  "admission_root": "CANONICAL_ADMISSION_DIRECTORY",
  "powershell": "POWERSHELL_EXECUTABLE",
  "collector": {"path": "ABSOLUTE_COLLECTOR_PATH", "sha256": "COLLECTOR_SHA256"},
  "process_observer": {"path": "PROCESS_OBSERVER_SCRIPT", "sha256": "OBSERVER_SHA256"},
  "max_executables": 20,
  "headroom_bytes": 17179869184,
  "minimum_estimate_bytes": 1073741824,
  "rss_to_commit_safety_factor": 2,
  "owner_launch_receipt": "OWNER_LAUNCH_RECEIPT_PATH",
  "parent_collector_receipt": "PARENT_CFEC_RECEIPT_PATH"
}
```

The launch receipt must identify a matching parent reservation with matching owner,
20 jobs, collector receipt path, and exact parent request hash. The pinned
`lib/executable-batch-processes.ps1` observer obtains live process start times and
ancestry. The owner PID/start must match the reservation exactly; the current
runner must descend through the recorded collector before reaching that owner.
Ancestor creation times reject recycled parent PIDs. The collector command must
name the pinned absolute helper path, no work timeout, and terminate-job policy.
The request must bind this runner, packet path and config hash. The outer owner
must validate request file hashes and shared admission under its lock. Standalone
execution without this owner/collector contract is unsupported.

`tasks.json` contains a `targets` array. Each target binds `packet`, `request`,
`request_sha256`, `producer_sha256`, `source`, `backend`, `entry`, `cache_lease`, and
`options` (`threads:1`, `hir_sharding:0`, `parse_sharding:0`,
`streaming_surfaces:1`). A child request binds `threads:1`, `command`, `cwd`, and
file-leaf SHA-256 hashes in `files`. Its optional `preflight_command` overrides
`command + ["--preflight"]`. Preflight uses the same `cwd` and inherited-plus-request
environment as actual execution. Empty manifests are rejected explicitly. Each qualification command must independently verify
its exact producer, frozen source authority and Hello proof before launching work.
Alternate Cranelift and LLVM targets in the manifest to exercise both backends as
memory admission expands. Manifest ordering is not proof of actual concurrency;
report `batch-state.json` and child PIDs.

Child outputs use `artifact/compile.rss.env`, optional `artifact/run.rss.env`, and
`results.json`. Result fields include `compile_exit`, `sanity_exit`,
`terminal_status`, `binary_linked`, `binary_sha256`, and `sanity_pass`. Ordinary
compiler/link failures continue only with verified quiescence. Missing results,
missing receipts, contradictory child exit/success, or retained cache leases block
further admission. Parent batch completion means all tasks were collected, not
that all tasks passed; consumers must inspect every result.

## Caches, cleanup, and resume

Preserve cache entries and failed logs. The compiler owns producer/source/options
identity validation. Never rewrite cache stamps. An output directory or retained
cache is not evidence of a cache hit. Use a separate exclusive lease for each
entry/backend writer. `lib/executable-batch-lease.shs` removes an owned lease only
before native launch or after quiescent/error-free RSS closure; acquisition failure
must not register cleanup for somebody else's lease. Leave interrupted leases for
explicit recovery after the original collector has closed its entire tree.

A compatible success skip additionally requires identical producer, source,
backend, entry and options, matching actual binary hash, linked binary, successful
sanity evidence, and closed receipts. A new producer or changed worker options
requires fresh qualification. `reuse_success` may bind a prior receipt and binary;
otherwise no success is assumed. A terminated batch itself requires a fresh,
reviewed successor packet; this helper does not blindly resume active outputs.

Separate parse/HIR/mono/MIR/codegen failures from actual linker diagnostics. Do not
call an access violation before MIR completion a link failure. No export, symbol,
ABI or duplicate-definition bug is established until a linker was actually reached.

## Focused checks and limits

```text
python scripts/bootstrap/tests/executable-batch-test.py
python scripts/bootstrap/tests/executable-batch-lease-test.py
python scripts/bootstrap/tests/executable-batch-owner-test.py
```

On Windows set `SIMPLE_BOOTSTRAP_BASH` to the installed Git Bash executable if PATH
selects the WSL launcher. Policy tests cover the group ceiling, initial measurement,
memory queuing without termination, ordinary failure continuation, unverified
child crash blocking, contradictory success, exact resume identity, and lease
quiescence. Shell tests exercise real cleanup with ownership/quiescence/error
combinations. Canonical collector tests remain the authority for Windows Job tree
reaping; these focused tests do not claim end-to-end product qualification.

Ownership tests reject missing owners, reused owner/collector PIDs, unrelated
ancestry and unbound commands, and execute a real preflight cwd/environment probe.
Set `SIMPLE_BOOTSTRAP_POWERSHELL` to enable the Windows live-observer test.
