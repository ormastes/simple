# Native selective MIR process qualification

**Status: UNRUN — executable source and manual prepared only.** No admitted
candidate build, test execution, generated-doc validation, performance result,
or release qualification is claimed by this document.

The candidate scope is the builtin LLVM/Cranelift native object boundary.
An explicit backend plugin path is refused by shared producer/worker/link
eligibility even when the requested backend has one of those names. The BOOT
profile matrix supplies OS environment flags; it does not reproduce or qualify
the Phase 3 `--internal-environment-variant-policy-v1` facade handoff. Exact
internal-policy activation remains a separate artifact qualification gate.

Executable: `test/03_system/native/native_mir_selective_process_spec.spl`.
Fixture: `test/fixtures/compiler/mir_selective/`.
Evidence class: **actual native process**, when executed by the qualified
pure-Simple SSpec engine. Loading the file alone provides no execution evidence.

## Qualification inputs

Every input below is mandatory. Missing values fail; no opt-in skip exists.

| Input | Contract |
| --- | --- |
| `SIMPLE_BINARY`, `SIMPLE_TEST_BINARY` | Same admitted engine pathname |
| `SIMPLE_TEST_BINARY_SHA256` | Exact immutable engine SHA-256 |
| `SIMPLE_MIR_SELECTIVE_TEST_BIN` | Distinct candidate-producer capability; no Rust seed |
| `SIMPLE_MIR_SELECTIVE_TEST_BIN_SHA256` | Exact immutable candidate SHA-256 |
| `SIMPLE_MIR_SELECTIVE_TEST_RUNTIME_PATH` | Qualified runtime-authority directory |
| `SIMPLE_MIR_SELECTIVE_TEST_RUNTIME_MANIFEST` | Root-qualified manifest for that authority |
| `SIMPLE_MIR_SELECTIVE_TEST_RUNTIME_MANIFEST_SHA256` | Exact pinned authority-manifest SHA-256 |
| `SIMPLE_MIR_SELECTIVE_TEST_TIMEOUT_MS` | Explicit positive outer process deadline |
| `SIMPLE_MIR_SELECTIVE_PARENT_KIB`, `SIMPLE_MIR_SELECTIVE_WORKER_KIB`, `SIMPLE_MIR_SELECTIVE_EXPORTER_KIB`, `SIMPLE_MIR_SELECTIVE_PHASE_KIB` | Explicit positive admitted phase estimates |
| `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` | Explicit positive enforced process-tree limit |
| `SIMPLE_MIR_SELECTIVE_DISK_BYTES`, `SIMPLE_MIR_SELECTIVE_DISK_RESERVE_BYTES` | Explicit positive transport envelope and reserve |

The owner must qualify SCV, manifest issuer, runtime payload hashes, ABI,
architecture and engine activation before execution. These values identify
capabilities; setting environment values does not create qualification or
enforce a process-tree memory ceiling. Run under the owner's real process-tree
watchdog. The spec checks binary and manifest hashes again without changing
active builds. Candidate children receive the candidate as `SIMPLE_BINARY`;
the outer engine remains the admitted engine. `SIMPLE_NO_STUB_FALLBACK=1` is set.

## Scenario: LLVM semantics, order, overlap and cache states

Run the matrix once per explicit profile below, with the same profile applied
to serial references, selective coordinator/children and corrupted-export/link
worker invocations. Inherited direct-IR, skip-pass, stub and streaming overrides
are cleared. The source entry remains the fixture's non-bootstrap `main.spl`.

| Profile | `SIMPLE_BOOTSTRAP` | `SIMPLE_BOOTSTRAP_STAGE4` | Serial behavior to preserve |
| --- | --- | --- | --- |
| Normal | `0` | `0` | Ordinary complete post-MIR pass chain |
| Bootstrap flat explicit entry | `1` | `0` | Original flat policy skips borrow/async/optimization/AOP/debug passes |
| Stage 4 | `1` | `1` | Ordinary complete post-MIR pass chain |

Each backend/profile pair has a private scope. Context and ordered-input
comparisons occur only within that pair; different profiles legitimately have
different context authority. The six pairs require 48 real native builds in
total, plus production refusal invocations. They remain **UNRUN**.

1. Require exact qualified engine, candidate and runtime artifacts.
2. Compile the serial fixture with LLVM and execute the actual native binary.
3. Repeat the serial build warm and compare native stdout, stderr and exit.
4. Build selective jobs 1, 2 and 15, cold then warm for each job count, using
   identical backend, ABI, source closure, output pathname and cache pathname.
   All serial/selective invocations use the established `--no-incremental`
   parent policy to bypass final-executable warm receipt reuse. Warm means the
   HIR/object stores remain populated; the actual coordinator still executes.
5. Require every native run to print `mir-selective-native=pass` and exit zero.
6. Compare the sealed ledger identity and ordered actual object sidecar inputs
   across all six selective runs. Require PASS terminals and existing objects.
   The identity binds the complete sealed manifest, context and declaration
   authority, including the producer's original source-barrier order.
7. Require distinct worker OS PIDs, absent worker PIDs, valid timestamps
   around actual body decode/lowering, and overlapping intervals for jobs 2/15.
   Count active intervals to require peak lowering concurrency at most jobs.
8. Preserve raw ledger copies, intervals, terminal/object records, build logs
   and semantic link receipts before clearing only this spec's private cache.

Fixture assertions exercise imported classes with field defaults, imported
payload enums and aliases, parameter defaults, generic specializations through
aliased imports for both integer and text, entry ownership, a mutable static
shared by writer and reader modules, and a provider constant. The fixture
returns a distinct failure exit for each semantic check.

The liveness oracle uses canonical `process_pid_exists`, whose documented
contract accepts arbitrary OS PIDs (`kill(pid, 0)` with a `ps` fallback), and
first requires the spec's own OS PID to exist. It does not pass raw receipt PIDs
to the runtime-owned child-handle `process_is_running` API. PID reuse causes a
conservative failure. PID absence at observation is not a child-handle wait
receipt; coordinator crash/timeout reaping evidence remains a separate gate.

## Scenario: Cranelift parity

Repeat the complete scenario using Cranelift, retaining that backend for both
serial and selective builds. No LLVM/Cranelift object-byte equality is claimed.
Neither backend has an established debug/timestamp normalization contract here;
comparison concerns actual executable behavior, context and ordered inputs.

## Failure matrix: actual exported artifacts

For each backend/profile, copy the successful jobs-1 warm export and invoke the actual
production worker with the same source/backend/runtime/cache arguments and a
fresh private queue. No fake compiler or production injection hook is used.

| Mutation | Required result |
| --- | --- |
| Missing manifest | Nonzero worker exit, selective-MIR diagnostic, no artifact publication |
| Truncated manifest | Same |
| Stale source identity | Same |
| Stale context identity | Same |
| Missing declaration artifact | Same |
| Truncated declaration artifact | Same |
| Missing all provider bodies | Same, regardless of LPT claim order |
| Truncated all provider bodies | Same, regardless of LPT claim order |

These cases prove worker refusal before publication. They do **not** prove a
coordinator reaps siblings after an injected worker failure or timeout.

## Failure matrix: final-worker inventory admission

Copy the actual successful jobs-1 warm ledger, retaining its exact context and
every valid PASS terminal/object sidecar. For one copy, remove the last physical
emission from `inventory`. For another, exchange the first two physical
emissions. Keep the admitted export unchanged. Remove the prior executable and
invoke the production final worker through `SIMPLE_MIR_SHARD_LINK` with identical
profile/backend/source/cache/runtime arguments. Require nonzero exit, a
selective-MIR admission diagnostic, no artifact-publication receipt and no
executable. A self-reported partial or reordered PASS inventory cannot establish
the complete manifest's physical schedule. Retain both refusal logs.

## Scenario: actual ordinary bootstrap-entry refusal

Request the actual `src/app/cli/bootstrap_main.spl` entry under bootstrap-flat
flags with the real `src/compiler`, `src/app` and `src/lib` source roots.
Require the production selective eligibility gate to fail with a selective-MIR
diagnostic before publishing an export bundle or MIR worker schedule, and
without artifact publication or an executable. This is a real source request;
no fake compiler, synthetic shortcut marker or source-text assertion stands in
for execution. This potentially substantial source-closure scenario is **UNRUN**.

## Scenario: resource admission refusal

Launch the actual coordinator with a phase envelope of 1 KiB and a parent
estimate of 2 KiB. Require nonzero exit, an admission-refusal diagnostic, no MIR
worker schedule announcement and no executable. Retain its log. This proves
the refusal branch only; it does not measure or establish real resource usage.

## Outstanding evidence gates

All executable scenarios above remain **UNRUN**. Additional required gates are:

- Real child nonzero/crash while siblings are live, with all children reaped and
  no final link admitted.
- Real child timeout under the production coordinator, with kill/wait evidence
  for every started process and no orphan children.
- Real transient-arena failure with preserved diagnostic ownership, complete
  cleanup and no final link. No test-only production hook has been introduced.
- Measured cold/warm startup, representative compilation latency and maximum
  RSS for the whole process tree under an externally enforced limit.
- Startup/ABI/SCV admission of the exact candidate and qualified runtime bundle.
- Execution with the active compiled SSpec engine and successful SPipe manual
  generation reporting zero stubs. This manual has been written by hand because
  the owner explicitly prohibited execution during spec preparation.

| Requirement | Executable coverage | Current evidence |
| --- | --- | --- |
| REQ-MIR-SELECTIVE-001 | LLVM/Cranelift × normal/bootstrap-flat/Stage 4 matrices; actual bootstrap and resource refusals; bundle and final-ledger corruption subcases | UNRUN |

<details>
<summary>Execution and evidence policy</summary>

Use the qualified engine's actual SSpec execution entrypoint. Do not substitute
file-loading success, source-text checks, scheduler simulations, seed binaries,
or preexisting build artifacts. Preserve the printed private evidence directory
after execution. A missing interval, no actual overlap, differing context/order,
unreadable artifact, missing backend, bad hash or absent capability is a failure,
never a skip or success. The complete native fixture may expose existing native
compiler defects; record those defects instead of weakening the oracle.

</details>
