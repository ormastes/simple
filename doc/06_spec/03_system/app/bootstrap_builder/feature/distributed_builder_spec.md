# Native bootstrap builder lifecycle

Source: `test/03_system/app/bootstrap_builder/feature/distributed_builder_spec.spl`.

Status: authored manual, native execution and SPipe generation pending. This
document is not a PASS receipt. General SPipe/docgen requires an admitted tooling
runtime; a preceding compiler may build the focused native qualification fixture
without granting general tooling admission.

## Run the lifecycle qualification

Build `test/fixture/bootstrap_builder/fixture_program.spl` as a native executable
and `test/fixture/bootstrap_builder/qualify.spl` as a separate native executable.
On Windows build `qualify_windows.spl` instead; it injects the Windows process
port into the same shared entry and harness. The portable entry does not import
Windows process providers. The harness uses opaque owned process tokens and
preserves typed spawn, wait, and termination failures; no failed operation becomes
a guessed PID or successful exit. These entries import the shared
`test.fixture.bootstrap_builder` modules; include the repository
test source root when resolving that namespace. The manager must already be a
compiled native artifact from its recorded producer. Never run these fixtures
through the Rust seed interpreter or treat an interpreter run as native lifecycle
evidence. The user-authorized Phase 1 seed may compile these native bootstrap
fixtures and the manager. That bootstrap-only exception does not grant general
tooling or release admission.

Set absolute paths in `SIMPLE_NATIVE_BUILD_MANAGER`,
`SIMPLE_BUILDER_FIXTURE_PROGRAM`, `SIMPLE_BUILDER_QUALIFIER`,
`SIMPLE_NATIVE_BUILD_MANAGER_HOSTS`, `SIMPLE_NATIVE_BUILD_MANAGER_PRODUCER`,
`SIMPLE_NATIVE_BUILD_MANAGER_SOURCE_IDENTITY`, `SIMPLE_NATIVE_BUILD_MANAGER_LLC`,
and `SIMPLE_BUILDER_QUALIFICATION_ROOT`.
The hosts file is a valid encoded `BuildRunV1` template using the required
`SIMPLE-BUILD-RUN-4` wire format and each host's exact `worker_digest`.
Its placeholder task carries an explicit `memory_limit_bytes` cap in the
inclusive range 1..1125899906842624. The compiled manifest emitter creates
that template with `--template WORKER WORKSPACE OUTPUT SLOTS --memory-limit-bytes N`;
one-task `--job` and `--job-from-inventory` calls also require that flag.
The inventory-backed call additionally requires `--links-inventory REL`, even
for an empty link list. It pins the regular and link inventory files and
declares each link's exact raw target and resolved in-root path. The typed
Phase 2 authority receipt and compiled pre/post verification prove the full
regular target set, including `examples/10_tooling/`; the generic task alone
cannot prove completeness. Tasks use `SIMPLE-BUILD-TASK-3`, and prior task/run
headers reject rather than inferring a cap or link list. The cap and links are
bound to task identity and wire admission;
this manual does not claim native memory enforcement or a completed run.
By default each local host selects the manager image. To qualify a separate
native worker, set both `SIMPLE_NATIVE_BUILD_MANAGER_WORKER` and
`SIMPLE_NATIVE_BUILD_MANAGER_WORKER_SHA256`; every local host must select that
exact path and digest. The source identity file
is the retained deterministic closure digest list from the manager build.

Run the qualifier with `all` to execute seven cases and emit a receipt only if
every case passes. A named case runs independently and never emits an overall
qualification receipt. Every run gets its own exclusively claimed output root;
evidence and caches remain there on failure.

| Case | Manual flow | Checked evidence |
| --- | --- | --- |
| Local execution | Run dependent native tasks through the manager; then supply a mismatched worker image digest. | Zero exit and verified successful output in the positive case. The mismatch must fail without producer execution or publication; an empty worker digest must fail codec validation. |
| Cache reuse | Resume a successful run without changing inputs or output. | Explicit verified-hit event, unchanged output including producer PID, successful terminal ledger. |
| Worker failure | Wait until the native producer starts, then request cancellation through its owning worker. | Actual exit 125, compiler tree reap marker bound to task and host, FAILED/BLOCKED ledger, no descendant dispatch or publication. |
| Restart | Terminate the owned manager while its producer waits; launch a replacement against the same state. | Exact fresh challenge acknowledgement, original producer marker, unchanged attempt, successful final ledger. |
| Keep-going | Execute a failing root, its dependent, and an independent root. | Actual producer exit 23; FAILED/BLOCKED/SUCCEEDED ledger and independent output. |
| Fail-fast | Run the failure graph with one slot. | FAILED/BLOCKED/BLOCKED ledger; neither pending task dispatched or published. |
| Cache invalidation | Corrupt one cached output and resume. | No admission of corrupted bytes, successful reconstruction, final output hash matching admitted receipt. Verified retained-artifact restoration requires its explicit event and a single verified cache hit; fresh execution requires zero hits. Conservative refusal alone fails this continuation gate. |

The one-slot policy cases deliberately reduce the selected local host's capacity
to make undispatched work observable. These cases do not certify configured
throughput. Compiler cache counters remain unknown unless independently measured;
receipt reuse is not inferred from file counts.

## Receipt and limits

The native harness emits `qualification.env` only after the actual checks above
and rehashes the manager, fixture executable, host template, producer, source
identity file, and llc before emission. The receipt binds the evidence log hash
and exact PASS line for each case. It also rechecks each configured worker image
against its frozen host digest and binds a separate image's path/hash when used.
The approved producer metadata is `producer_kind=bootstrap-phase1-seed`,
`producer_phase=stage1`, `use_scope=bootstrap-manager-only`, and
`retained_through=stage4`; the producer path must identify the actual authorized
seed used to compile this manager. Shell validation may consume that receipt;
it must not manufacture one.

This suite rejects SSH hosts and emits `execution_mode=local`. Configured remote
execution remains a separate required gate for distributed completion; Windows
or WSL protocol fixtures do not prove a real remote worker executed. Module/SCC
crash isolation and full bootstrap are also separate gates. No remote PASS marker
or success placeholder is present here.

Requirement traceability: REQ-BBM-003 local execution only; REQ-BBM-004 worker
cancellation and reaping only; REQ-BBM-005 failure policies; REQ-BBM-006 receipt
reuse and output corruption only; REQ-BBM-008 live manager restart only. This
suite alone does not establish complete coverage of any broader requirement.
