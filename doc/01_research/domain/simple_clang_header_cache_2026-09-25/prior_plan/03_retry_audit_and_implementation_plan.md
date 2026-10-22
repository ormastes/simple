# Report 3 — Failure recovery, repository audit, implementation waves, and acceptance tests

**Date:** 2026-09-25  
**Audit commit:** `ed75897fe050d874ce7c7bcd90c2b30953ad65ce`  
**Scope:** Targeted read-only inspection of named files and live repository/ruleset metadata. No build, benchmark, test suite, hook installation, or remote-setting mutation was performed.

## 1. Failure and retry contract

The action key identifies the computation; the attempt ID and monotonic fence identify who may publish one execution's result. Keep those separate. A distributed request can execute more than once after connection loss; promise **at-least-once execution with one accepted fenced publication**, not exactly-once execution.

Record events outside the compiler group before acknowledging action ownership. The surviving node agent/main scheduler must know every action that was running when a group disappeared. A completion message without durable publication is a candidate result, not a completed action.

### Group failure sequence

1. Detect exit, broken IPC, heartbeat loss, memory corruption evidence, or an unresponsive deadline. A missed heartbeat alone may be a pause, not death.
2. Stop assigning work and revoke the group's publication epoch. Reject late results under the old fence.
3. Inventory all uncommitted actions. They become infrastructure-interrupted, not automatically compiler/test failures.
4. Terminate and reap the group and its child processes where required. Preserve bounded diagnostics, task IDs, input/manifest references, and crash dumps subject to confidentiality policy.
5. Discard suspect group-local mutable state. Do not reuse it merely because a lock can be reacquired. Verified immutable store objects can remain; quarantine already-published objects too if the evidence implicates earlier corruption.
6. Restart from the pinned toolchain and verified resources. Retry interrupted compilation tasks in fresh isolated processes for diagnosis, subject to the limits below.
7. Resume grouped mode only after the provider/group passes health policy. Repeated crashes open a circuit breaker and require investigation.

A segmentation fault, fatal assertion, or unsafe thread termination is not safely handled by replacing only the offending thread. A stuck task gets cooperative cancellation first; if it cannot acknowledge, terminate its failure domain rather than asynchronously killing a thread while it may own locks.

### Retry matrix

| Failure class | Automatic action | Result/admission rule |
|---|---|---|
| Ordinary syntax/type/compile diagnostic | No retry. | Deterministic code failure, not infrastructure. |
| Test assertion or golden mismatch | No automatic pass-seeking retry. Optional diagnostic rerun only. | Preserve original failure. |
| Group process crash | Fresh isolated process using identical action/toolchain/input roots. | Original attempt retained; all interrupted peers tracked. |
| Isolated compiler crashes again | At most one alternate healthy-node diagnostic attempt when justified. | Report reproducible tool/action failure; no infinite retry. |
| Success only in isolated/fresh mode | Re-run required evidence in qualified isolation. | Mark `ISOLATION_SENSITIVE`; grouped provider remains quarantined. |
| Node disconnect/preemption | Retry replay-safe actions on a compatible node after fencing. | Old node cannot publish into the new attempt. |
| OOM/resource exhaustion | One policy-bounded larger-memory or lower-concurrency retry. | Record both attempts; do not conceal a new memory regression. |
| Deadline exceeded | Cancel/fence; retry only if infrastructure delay is established. | Do not silently increase a semantic test timeout and claim the same validation. |
| Transient CAS/network failure | Bounded backoff/jitter and verified redownload. | Exhaustion is incomplete infrastructure, not a test pass. |
| Digest/manifest mismatch | Quarantine offending object/mapping; fetch from an independent admitted source or rebuild. | Integrity incident; never accept “close enough”. |
| Equal action key, different outputs | Disable/quarantine that mapping; preserve both results and environments. | Reproducibility/key-completeness failure. |
| Missing/incompatible requested toolchain | Install/fetch exact qualified digest or choose compatible node. | No silent fallback to arbitrary installed compiler/lib. |
| Hardware test interruption | Fence device lease; confirm prior operation stopped; reset/health-check before reuse. | May require manual recovery; never speculative duplicate execution. |
| Sign/publish/deploy action interruption | Query durable operation state and reconcile idempotency key. | Ordinary compile retry policy is forbidden. |

Default budgets should be small and class-specific: for example one isolated crash retry and one relocation after a node failure. These values are proposed initial policy. Timeouts, OOMs, and assertions must not all collapse into a generic “retry three times”.

### Publication fencing

Use `(job_id, action_key, attempt_id, node_epoch, group_epoch, fence)` and an expected current publication version. The broker atomically accepts a manifest only when that tuple is current, all payloads are available and verified, and the required output set is complete. Deduplicate identical accepted results. No worker may overwrite a READY immutable payload.

Lease expiry removes permission to publish but does not make a shared-memory pointer safe to reuse, nor stop a physical device. Confirm process death/quiescence for memory reuse; use a device agent/watchdog and explicit reset acknowledgment for hardware. A PID is insufficient identity because it can be reused.

### Shared-state owner death

A shared slot must have a generation, owner epoch, and explicit construction/publish state. If a producer dies before READY, discard/rebuild its partial output. Readers must never interpret WRITING bytes as a valid cache object. Publication requires release/acquire synchronization or the platform's equivalent.

A robust mutex can report owner death, but recovery still needs a consistency protocol. Mark unrecoverable structures invalid and rebuild from durable immutable manifests rather than assuming the mutex repaired them. [W14]

Keep leases/pins in the surviving broker when possible. Crash-prone workers should not be able to strand a global refcount indefinitely. Cross-process mutable queues/indexes are an optimization only after owner-death, ABA/generation reuse, and eviction races are tested. The simplest correct brokered implementation is the initial reference.

## 2. Current Simple evidence and gaps

All code findings below refer to the pinned audit commit. Live GitHub ownership/ruleset observations are dated reads, not properties pinned by the commit. Older design documents are evidence of intent, not evidence that their reported implementation status remains current.

| ID | Observed evidence | Consequence / required work |
|---|---|---|
| A01 | `target_executor.spl` returns an empty action digest and `target_action_reusable` returns false. [R02] | Complete authoritative imported-closure input identity before enabling executor-level cache hits. This says nothing about every lower-level cache being disabled. |
| A02 | The same executor rejects dependency-bearing targets with `dependency-input-unsupported`; its diagnostic names missing `--input-manifest`. [R02] | Add actual dependency artifact consumption, not just topological execution order. |
| A03 | Its candidate output path is qualified by PID. [R02] | Before concurrent actions within one process, add attempt/action IDs and exclusive creation; PID alone collides for parallel invocations of the same output. |
| A04 | The inspected fast script documents/defaults to syntax-only checks and mirror/import-based unit/feature mapping. [R03] | Add an admitted semantic compiler path and authoritative test impact selection. Do not describe syntax-only PASS as compilation correctness. |
| A05 | That script treats missing mappings/zero relevant execution and budget overrun as unsuccessful; it binds a 60-second receipt budget. [R03] | Preserve fail-closed intent while separating code failure, incomplete work, and genuinely non-applicable changes. |
| A06 | `pr-fast-check.yml` verifies signed local receipts using base-owned code and skips fork PRs. [R04] | Keep its trust boundary, add real disposable execution for forks/seed availability, and avoid skipped-required-check holes. |
| A07 | The action-key module uses a canonical, domain-separated encoding; its textual source-interface extractor explicitly omits field lines. [R05] | Reuse the encoder but do not base layout-sensitive avoidance on that extractor. Qualify resolver/type-derived summaries. |
| A08 | The remote client recomputes artifact byte digests, but the inspected function compares the manifest's claimed digest rather than visibly recomputing canonical manifest bytes; it does not consume `receipt_digest` to verify a signature. [R06] | This function alone is not a complete trusted remote admission boundary. Audit its callers/transport/publisher, add explicit staged validation types, and test tampering before enabling the new remote path. |
| A09 | That client's milestone interface is fetch-only and describes injected/fake transport scope; artifact bytes are represented as text in its DTO. [R06] | Treat it as a cache building block, not proof of a production remote execution service. Add binary-safe payload handling and real transport qualification. |
| A10 | Existing pre-push dispatcher contains hook-preservation, Git-environment cleanup, and recursion defenses. [R08] | Extend it; do not introduce another hook chain or duplicate installer. |
| A11 | Existing `land.shs` gates committed refs through a wrapper seam and documents the JJ/Git hook gap. [R09] | Integrate the policy runner there and test supported clients end-to-end. |
| A12 | A canonical `must_check_gates.sdn` already exists with tier/obligation metadata. [R10] | Add a versioned plan there; preserve obligation coverage during tier migration. |
| A13 | Existing targeted-build design specifies typed facets and compatibility results. [R11] | Continue it rather than inventing a conflicting incremental-build model. Its August implementation notes are not treated as September proof. |
| A14 | `.gitmodules` includes core-adjacent demos and independent applications/tools. [R07] | Classify by coupling; do not collapse all submodules or use them solely to hide slow tests. |
| A15 | Repository metadata says public and user-owned. [R01] | Native GitHub merge-queue eligibility must not be assumed. Use current protected serialized integration. |
| A16 | Live main ruleset requires two named structural/review checks, has strict required-status policy, and has a bypass role. [R12] | Introduce new admission as a controlled ruleset migration; audit bypass usage. No complete compile/test requirement was inferred from workflow filenames. |

This is a targeted audit, not a whole-repository call-graph or security audit. In particular, A08 identifies what one function does and does not establish; it does not claim a remotely exploitable end-to-end vulnerability without inspecting the complete admission path.

## 3. Important corrections to earlier session claims

| Earlier simplification | Final position |
|---|---|
| “Unchanged public interface means only direct tests.” | Compile avoidance and behavior-test invalidation are separate graph queries. |
| “Process sharing gives excellent isolation.” | Shared writable bytes can carry corruption across processes; isolate authoritative state and validate publication. |
| “Any aligned atomic works between processes.” | The specific host/compiler/width/synchronization ABI must be qualified; fallback locks may be process-local. |
| “One Clang AST can be reused among compile threads.” | Reuse serialized PCH/PCM/BMI/preamble resources; use private mutable frontend contexts. [W01] |
| “Threaded group is always faster.” | It is the preferred architecture to qualify, not a measured result. Keep a comparable singleplex baseline. |
| “A retry pass means the failure vanished.” | Preserve flaky/isolation-sensitive evidence and quarantine the unsafe execution mode. |
| “A shared-memory descriptor can just contain a handle integer.” | Transfer a real scoped OS capability, then bind it to the SDN descriptor. |
| “A signature proves tests ran.” | It proves issuer/message authenticity; trust the executor boundary, not the signature alone. |
| “LLVM-style monorepo implies native GitHub merge queue.” | Repository structure and GitHub product eligibility are unrelated. [W23] |
| “Missing worker or no changed `.spl` can simply pass.” | Classify applicability and missing evidence explicitly. |

## 4. Implementation ownership and merge order

Use isolated worktrees/workspaces for each work package. No parallel package creates its own alternative schema, action hash, CAS, or scheduler ledger. Publish the shared contracts before parallel implementation. The following paths are **proposed ownership locations** except named existing files explicitly cited; resolve final placement against the active source architecture during W0.

| Package | Primary owner / area | Dependencies | Deliverable and gate |
|---|---|---|---|
| W0 — Contract and baseline freeze | Build/cache architecture owner; existing canonical identity + must-check registry | None | Requirements crosswalk, source snapshot, SDN schemas, threat/failure model, current benchmark harness; reviewers agree on field semantics. |
| W1 — Authoritative input/dependency closure | Resolver/semantic owners; existing target and interface modules | W0 | Snapshot-bound InputManifest, typed edges, old/new graph, negative probes; exact changed input always invalidates the necessary action. |
| W2 — Target artifact consumption and exact cache reuse | `src/app/build/targets/` + native-build owner | W1 | Real input-manifest consumption, action-scoped candidate paths, existing CAS integration, validated local hits; no false hit in mutation suite. |
| W3 — ResourceShare and sosix primitives | Shared-runtime/FFI owner; proposed resource-sharing library | W0 | ResourceStore/State APIs, handle/lifetime model, RO mappings, brokered mutable coordination, portability tests. |
| W4 — Reference isolated executor and fencing | Execution/runtime owner | W0, W2 | Durable attempts, cancellation, private outputs, publication fences, process-tree cleanup; fault-injection suite passes. |
| W5 — Simple persistent group provider | Compiler/runtime owners | W2, W3, W4 | Per-action state separation, qualified thread pool, bounded startup caches, grouped/isolated parity and reset tests. |
| W6 — Clang resource adapter, then grouped provider | C/C++ toolchain owner | W2, W3, W4 | First subprocess + PCH/PCM/BMI reuse; then pinned in-process adapter with private AST/LLVM contexts and reentrancy qualification. |
| W7 — Test impact and architectural lint | Dependency/test owner | W1, W2 | Unit/contract/layer/feature ownership, runtime-edge selection, fixture/configuration edges, unknown fallback; shadow/full comparisons. |
| W8 — Local hook and GitHub integration | CI/repository owner | W4, W7 | One gate policy, snapshot receipts, draft/ready rules, fork-safe runner path, always-run admission aggregation; no weakening of existing checks. |
| W9 — SDN remote execution and idle hosts | Distributed runtime owner | W3, W4, W5 | Node registration, exact tools, lease/fencing, native/cross selection, secure isolated pools, bounded transfer/cache behavior. |
| W10 — Qualification, performance, release | Independent verification owner | W5–W9 as enabled | Evidence bundle, supported-host matrix, under-60s measured eligible cases, release bootstrap/promotion, rollback drills. |

Parallel work after W0: W1, W3, and reference failure-ledger design can proceed independently under frozen contracts. W2 is the first production speed milestone. W5/W6 should not delay fixing semantic CI and selected tests. W9 is not a prerequisite for a useful local build system. Kubernetes worker provisioning follows W9 and is optional.

### Suggested integration points

Extend existing `target_executor`, target resolution, canonical identity, cache publication/lease/journal modules, and must-check scripts. Add action-context/resource/provider interfaces as reusable library services, not compiler-specific state inside the main scheduler. Use sosix for process/memory/IPC backends. Reuse existing compiler `.tld/.rr/.sreq` work without treating candidate code or design-only comments as admitted production behavior.

Document any changed on-disk or binary schema as a new version; do not silently reinterpret an existing cache. Bump or scope formats only when compatibility changes. Migration tools may read old data for inspection, but unqualified old results cannot bypass the new completeness/trust checks.

## 5. Required acceptance test catalogue

Each test below needs an executable fixture, expected outcome, owner, and machine-readable receipt. A checkbox in a report is not completion evidence.

### Identity and dependency correctness

| ID | Fixture | Required result |
|---|---|---|
| I01 | Same action under reordered SDN map fields/comments | Same canonical semantic key. |
| I02 | Swap include search order, add an earlier candidate | Resolution/action invalidates. |
| I03 | Change bytes while preserving mtime/size | Cache miss or strict revalidation; never stale reuse. |
| I04 | Delete/move a provider or gitlink | Old graph consumers are still invalidated. |
| I05 | Change only ordinary function body | Provider rebuilt; compatible caller compilation may remain; behavior-dependent tests rerun. |
| I06 | Change struct field type/offset or enum layout | ABI/layout consumers rebuild/reject. |
| I07 | Add overload/trait implementation or applicable pointcut | Candidate-set/absence witnesses invalidate relevant consumers. |
| I08 | Change macro/CTFE/generic/inline body | Semantic consumers rebuild. |
| I09 | Change compiler binary or live interpreted compiler source | Generated artifacts and candidate-tool tests rekey. |
| I10 | Change fixture, schema, build script, generated file, runtime library | Corresponding build/test closure invalidates. |
| I11 | Same output name compiled concurrently in one PID | Separate attempt-private candidates; no overwrites. |
| I12 | Missing graph history/incomplete extractor | Conservative plan or incomplete, never trusted negative selection. |

### Resource sharing and provider isolation

| ID | Fixture | Required result |
|---|---|---|
| S01 | Many simultaneous requests for one resource | One admitted producer; waiters get the same valid object. |
| S02 | Producer dies before READY | No reader observes partial bytes; resource rebuilds. |
| S03 | Eviction overlaps a live mapping | Mapping remains valid until lease ends. |
| S04 | Map same object at different virtual addresses | Offset-based references remain valid. |
| S05 | Same slot/PID is reused | Generation/epoch checks reject stale owners. |
| S06 | Cancellation of one single-flight waiter | Other waiters continue correctly. |
| S07 | Every compiler waits for a module build | No token starvation deadlock; module producers can run. |
| S08 | Alternating projects/macros/options in warm process | No semantic state or diagnostic leakage. |
| S09 | Random concurrent Clang/Simple workloads | Outputs agree with isolated qualified mode. |
| S10 | Raw-pointer/lazy-mutable AST sharing attempt | API/type/capability validation rejects it. |
| S11 | Cross-process mutable owner dies under lock | Owner-death detected; consistency repaired or state discarded. |
| S12 | Unsafe plugin or process-global option | Routed to isolated execution, not silently multiplexed. |

### Retry and distributed correctness

| ID | Fixture | Required result |
|---|---|---|
| F01 | Kill a group with several actions active | Every uncommitted action recovered once logically; no false test failures. |
| F02 | Delayed old worker returns after retry | Publication fence rejects its result. |
| F03 | Crash after CAS upload but before result commit | Restart reconciles without duplicate authoritative publication. |
| F04 | Assert-failing test passes on diagnostic rerun | Original failure retained; no automatic green. |
| F05 | OOM and retry with larger memory | Classified separately; limits and regression evidence recorded. |
| F06 | Thread hangs while owning a lock | Cooperative cancel then group termination; no forced thread reuse. |
| F07 | Equal key produces distinct output trees | Quarantine and reproduction package. |
| F08 | Network partition during hardware test | No second unfenced device owner; reset/reconciliation required. |
| F09 | Node has wrong compiler/SDK or binary ABI | Not eligible; no fallback to PATH. |
| F10 | Cross-compile succeeds without native test node | Build success, native validation incomplete. |

### CI, hook, and repository correctness

| ID | Fixture | Required result |
|---|---|---|
| C01 | Staged source broken, unstaged source fixed | Pre-commit detects staged failure. |
| C02 | Committed source broken, working tree fixed | Push/PR gate checks committed failure. |
| C03 | Non-`.spl`-only relevant change or docs-only change | Correct specific applicability, not zero-work error or blind success. |
| C04 | Test process exits zero with zero cases | Required execution fails/incomplete. |
| C05 | New source has no target/test owner | Owner mapping required or conservative fallback; cannot disappear. |
| C06 | Large change exceeds 60 seconds | Remaining actions reported; ready/admission blocked as incomplete. |
| C07 | Fork PR, policy rewrite, forged receipt, stale tree | Trusted admission rejects unauthorized/stale evidence. |
| C08 | Required child job skipped/canceled/missing | Aggregator does not emit successful admission. |
| C09 | Base advances after candidate passes | Candidate revalidated under strict protected integration. |
| C10 | `git`, `jj`, `sj`, `gh`, UI/API submission routes | Ultimate remote protections equivalent; local wrappers cannot bypass them. |
| C11 | Hook installer runs twice with a custom hook | Custom hook preserved; no recursion or process storm. |
| C12 | Submodule points to unpublished/dirty/moving revision | Pin/availability validation fails. |
| C13 | Release tag would refer to different tested bytes | Promotion rejects mismatch. |
| C14 | Bootstrap stage is served entirely from old action cache | Cannot claim an independent clean bootstrap run. |

### Proof and stress strategy

Use small formal models where they help: canonical field coverage, publication fencing, slot state transitions, lease/pin reclamation, and compatibility-check soundness assumptions. Proofs over a model do not establish that a source scanner found all real inputs or that a C++ provider is reentrant. Pair them with real process kill tests, randomized schedules, race sanitizers, corpus mutation, crash recovery, and differential clean-vs-cached builds.

## 6. Benchmark and rollout gates

Benchmark the same fixed source corpus and pinned toolchain in four modes: fresh isolated process, warm isolated singleplex process, grouped threads, grouped threads plus ResourceShare. Add remote execution only after local comparison is meaningful. Cover tiny modules, header-heavy C++, broad frontend changes, large links, and mixed tests.

For each workload record cold/warm conditions separately, at least P50/P95/P99 wall times, total CPU, disk/network bytes, peak private/shared memory, startup time, per-cache hits/misses, parser work, lock contention, queue time, and abort/retry costs. Report actual end-to-end timing rather than hiding bootstrap/download/setup outside the measured interval.

Promotion criteria:

* Zero known false cache hits in the required mutation corpus and reproducible differential runs.
* Zero lost/duplicated authoritative completions in failure injection.
* Provider qualification covers its advertised concurrency/isolation modes on each host class.
* No skip/fork/receipt route can satisfy complete admission without required evidence.
* Ordinary eligible warm preflight P95 is measured below 60 seconds; exceptions are explicitly classified.
* Memory/concurrency limits remain effective under worst-case parallel compiles and slow consumers.

If a precision or concurrency optimization fails, fall back independently: conservative full affected closure, uncached execution, singleplex process, local node, or already-qualified gate/seed. A release must not depend on an unavailable optimized mode.

## 7. Completion evidence package

Each work package delivers code, schema/version changes, a negative-test demonstration, a reproducible command manifest, actual result artifacts, performance data where relevant, and a rollback switch. An independent reviewer checks source provenance and validates at least one deliberately failing fixture before declaring the package complete.

The final system release includes the supported-host/provider matrix, test-selection confidence report, cache-soundness report, group-crash recovery report, fork/admission security report, and exact candidate promotion manifest. Do not label a scaffold, dry-run plan, or fake transport test “distributed build complete”.

## References

[R01]: https://api.github.com/repos/ormastes/simple "Simple repository metadata (read-only audit, 2026-09-25)"
[R02]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/app/build/targets/target_executor.spl "Simple named-target executor"
[R03]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/check/check-pr-fast.shs "Simple fast-PR checker; inspected lines 1–125"
[R04]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/.github/workflows/pr-fast-check.yml "Simple fast-PR GitHub workflow"
[R05]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/compiler/80.driver/cache/action_key.spl "Simple canonical action key and textual interface extraction; inspected lines 1–230"
[R06]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/compiler/80.driver/cache/remote/remote_client.spl "Simple remote cache client"
[R07]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/.gitmodules "Simple submodule registry"
[R08]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/hooks/pre-push "Simple pre-push dispatcher"
[R09]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/check/land.shs "Simple landing wrapper; inspected lines 1–95"
[R10]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/config/check/must_check_gates.sdn "Simple canonical must-check registry; opening portion inspected"
[R11]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md "Simple targeted-build/interface plan; opening 130 lines inspected"
[R12]: https://api.github.com/repos/ormastes/simple/rulesets/21573643 "Active main/integration-main ruleset, read on 2026-09-25"
[W01]: https://clangd.llvm.org/design/threads "clangd: threads and request handling"
[W14]: https://man7.org/linux/man-pages/man3/pthread_mutexattr_setrobust.3.html "POSIX/Linux robust mutex behavior"
[W23]: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue "GitHub merge-queue eligibility and CI integration"
