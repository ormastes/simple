# Phase 3 and incremental build completion plan

Status: ACTIVE. This is the replacement execution plan as of 2026-10-13. It supersedes the execution status of [the earlier agent plan](../agent_tasks/incremental_build_metadata_20261008.md) and [the earlier acceptance plan](../sys_test/incremental_build_metadata_20261008.md). Those documents are closed as execution plans and retained as historical requirements and test-design references. Closing a plan does not mean its features are implemented.

## Priorities and scope

1. Produce a usable Phase 3 compiler: repair object-generation failures, retain compatible successes, link the compiler, and compile/run Hello World with it. Land reviewed compile fixes on `release_phase3` through PRs as they become usable.
2. Complete TLDR, SCV and build-runner integration and demonstrate real compile performance without introducing logic or memory regressions.
3. Build supported Phase 4 tools using available Phase 1/2/3 compilers; collect object and link failures independently and run executable sanity checks as each becomes available.
4. Continue runnable host-appropriate Phase 1/2/3 tests. The six native test-product builds are DEFERRED by the user; they are neither passed nor completed. Phase 1 limitations require explicit unsupported-case records.

Known nonblocking memory inefficiency may be tracked and repaired after a usable compile fix lands, as requested by the user. A process crash or memory corruption is not a successful compile; isolate it with a recorded workaround or repair it. Source admission, digest and ownership failures cannot be relabeled successful. Every workaround needs a source tag, canonical bug record or explicit pending reconciliation, actual workaround commit, intended-code recovery reference, and background repair owner.

## Verified baseline and current candidates

| Work | Evidence and boundary |
| --- | --- |
| Phase 3 module objects | Sealed through67 aggregate: 2249 attempted; 447 PASS, 1761 FAIL, 41 interrupted, zero untried. Requested-object successes do not prove a full compiler or executable. |
| Failure grouping | 827 first-error signatures; more than 640 timeout rows have no proven root cause. Do not treat every row as a distinct defect. |
| Imported factory generic inference | Original native 10-module reproducer fails E-MONO-032/033. Caller-local cached HIR proves the imported factory's nominal return owner. Local Mono patch and six prevention cases exist; first diagnostic returned five passes and one test-selection failure. Failed-case-only correction and rebuilt-native qualification remain pending. |
| MIR record pointer crash | PR #3456 contains two complete-pointer constructor repairs. Private successor compilation reports compiled=4, reused=1309, failed=0; archiver launch then failed Windows OS206 command length. Job0 and unchanged source/tool pins are retained. Response-file archive, strict link and runtime regressions remain pending. This does not increase the legacy447 object total. |
| Relative import ownership | PR #3457 is a draft candidate. Native behavior, latency and RSS checks remain pending; it needs a successor compiler. |
| print_raw | Native portable target has a genuine unresolved-name failure. Seven real parser/HIR/MIR criteria and a private candidate are prepared. Baseline evidence is HOLD due to diagnostic truncation. No exact print_raw failure was found in1760 available legacy Phase3 failed logs, so no module-wide unblock count is claimed. Strict HM, dynamic NUL, interpreter parity and native ABI/output qualification remain open. |
| Materialization performance | One native three-file probe passed byte-integrity checks; wrappers21.233/48.752/13.019ms, inventory199.370ms. Native wall4.208s versus CPU0.281s. Three positives do not prove compile latency, identify the waiting cause, or certify negative/race behavior. |

Evidence locations are local retained artifacts under `build/native_probe/phase3-aggregate-through67-20261013-astra`, `phase3-affected-retry-20261013-sol`, `compiler-source-authority-20261013-astra`, and `phase1-current-whole-20261012-sol/native-materializer-profile-v1`. Original receipts, producer hashes and source membership remain authoritative; this table is a dated snapshot, not a live counter.

## Feature completion matrix

The entries below are incomplete until their end-to-end acceptance evidence exists. Authored source, a candidate, or a helper test is not full feature completion.

| Feature | Remaining integration | Completion evidence |
| --- | --- | --- |
| TLDR as imported header | Compile an entry SPL with validated dependency summaries; read generic/CTFE bodies only when required and explicitly recorded. Preserve standalone compiler support. | File-open trace proves ordinary imported source bodies were not parsed; emitted object and executable match reference behavior and diagnostics at equivalent coverage. |
| SCV source/TLDR generations | Include TLDR membership and source roots in immutable generation authority; use commit-based snapshots plus independently identified edits/new files. Validate content and membership, not timestamps alone. | Newer TLDR timestamp cannot hide changed-source syntax errors. Source/TLDR removal, changes, digest forgery and stale generation all reject or regenerate correctly. |
| Shared TLDR/AST artifacts | Reuse source parsing performed during summary generation in later source compilation; share frontend artifacts with test runner. Cross-host serialization excludes process-local IDs. | Actual parse counters show no duplicate parse for the same admitted input; portable AST round-trip works; target/layout mismatches reject object reuse. |
| Async build ownership | One publisher per complete action key, immutable waiter results, asynchronous reads and bounded queues; compiler works with and without build runner. | Real concurrent same-key requests build once; independent keys progress; cancellation, owner crash, SCC imports and stale epochs cannot deadlock or publish partial artifacts. |
| Cache invalidation | Capture source/dependency/read-facet, compiler, toolchain, target, configuration, aspect/static-guard and negative-query identities. | Body/public-signature/constant/initializer/overload/impl/aspect/config changes match uncached reference; no stale receipts or rewritten stamps. |
| IDE/SPipe edit tracking | Feed equivalent UTF-8 deltas to existing SCV owner; reconcile edits without hooks and watcher overflow with bounded overhead and durable recovery. | Equal semantic transitions yield equal canonical deltas; origins remain distinct; crashes/torn journals recover; hook CPU/RSS/latency measured. |
| Runner recovery and qualification | Preserve grouped workers normally; isolate unknown tasks after crash. Keep independent build/test tasks running and preserve nonzero aggregate failures. | One failure/crash does not suppress independent work; retry only affected failed stages; header may survive object failure without declaring object/link ready. |
| <=100ms entry compilation | Include startup, source admission, header validation, parse/lower, object emission and publication. Dependency preparation must precede measurement. | Bounded same-source p50/p95, CPU, RSS, bytes, opens, cache counts and lock waits; exactly one new entry object, zero hidden imported-body codegen. Cold and final-link costs reported separately. |
| Formal cache model | Model generations, header/object stages, publishers/readers, leases, cancellation and crashes against real owner interfaces. | Retained finite-model safety/liveness result plus real concurrency/failure tests; modeling does not prove complete semantic read sets. |

Carry forward every scenario and requirement in the historical acceptance plan, including snapshot separation, full diagnostic coverage, publication races, scope completeness, packed/hybrid parity and post-build qualification. No scenario is discarded by supersession.

## Parallel owners and execution sequence

| Lane | Ownership | Immediate next action |
| --- | --- | --- |
| Astra generic inference | Mono imported-callable return registry and its new regression specs | Run only the corrected failed criterion; review narrow transplant onto remote Mono, then qualify a coherent successor and real native event target. |
| Cached compiler successor | Private source/cache for two MIR pointer body fixes | Package the retained1314 output objects via exact response-file membership; strict-link genuine runtime/startup; run stored Optional/Result owner regressions and failed LSP case. |
| Builtin parity | print_raw HIR/MIR candidate and focused specs | Run the prepared seven new criteria; keep unresolved strict-HM/NUL/interpreter/native-output scope explicit. |
| Root | Scheduling, exact source/PR review, failure assignment and landing | Review results once, check caller compatibility and ownership, land usable owned fixes, then assign the next uncovered failure families. |

Do not create new worktrees. Preserve other sessions' dirty files and shared index. Reuse compatible idle caches; isolated writable outputs are required for concurrent jobs. A producer repair needs a new compiler containing it; compiling a test with an old immutable compiler does not apply the repair.

Requested parallel ceiling is40 jobs per applicable build lane, with80 available logical cores. Actual concurrency depends on reentrant backend ownership and measured memory; report real worker counts rather than assuming a flag means40 active workers. One process with four module-owning threads is a target topology only after ownership/cache tests qualify it. Do not multiply known multi-GiB workers beyond measured host capacity.

Retain the447 sealed successes. Retry affected failures after a concrete source/input/producer change; do not replay unchanged successes or unknown timeouts blindly. At most three repair/verify cycles per feature; after that, record the remaining bug and a reviewable mitigation rather than rename the feature to reset its budget.

## Landing and exit criteria

Each PR carries exact source scope, reproducer/prevention results, known issues, workaround/recovery links and unrun qualification explicitly. Check duplication, review comments and genuine failing checks before landing. Do not merge another session's active draft merely because it contains a useful candidate. Documentation landing is not compiler admission or a release tag.

Phase3 is complete only when the required compiler closure yields authenticated objects, its genuine compiler executable links, and that compiler builds/runs Hello World. Record unresolved optional/host-disabled modules separately using actual host configuration. Full feature completion additionally requires the matrix above and supported Phase4 build/sanity results. No overall goal-complete claim is authorized by partial object totals or this plan.


## Evidence reconciliation — 2026-10-26

The October 13 baseline above is historical. The latest retained whole-program
stage3 run failed with 3,104 MIR errors. An older stage2 comparison also failed
in that lane; a new-producer regression is not established. Smaller closure
results separate successful compilation from the remaining optional payload
pattern, method-resolution and substitution failures. See the
[retained evidence and full remaining acceptance ledger](../evidence/cache_perfile_phase3_reconciliation_2026-10-26.md)
and [updated cache/per-file index](cache/cache_perfile_plan_index_2026-10-25.md).
All feature-matrix and historical acceptance requirements remain in scope.
No Phase 3, per-file-default, SPipe verification, or overall completion is claimed.
