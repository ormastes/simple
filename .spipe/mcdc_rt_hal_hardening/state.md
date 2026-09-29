# Feature: MC/DC and RT-HAL Hardening

## Raw Request

Implement the planned but missing MC/DC feature completely with performance and memory efficiency as first-class constraints: support compile-time off with zero runtime/allocation overhead, compile-time on, and dynamically loaded aspect instrumentation with minimal overhead and no needless allocation. Improve the existing `rt(hal)` tag so C, Rust, and pure-Simple implementations can run in parallel while the pure implementation matures, compare their I/O, and permit configuration/customization without replacing pure Simple. In normal mode and above, require 100% MC/DC except explicit, reasoned, non-producible scenarios. Extract RT/HAL interaction tests into environment-access instructions executed by the environment, add a proper skip/exclusion expression that requires a reason, harden RT, and promote RT to mission-critical mode or higher unless explicitly specified, warning first and later becoming an error.

## Task Type

feature

## Refined Goal

Deliver production-grade pure-Simple MC/DC instrumentation, enforcement, RT/HAL differential execution, environment-mediated interaction evidence, reason-bound exclusions, and RT criticality hardening with proven correctness, zero-cost static disablement, and bounded enabled-mode time and memory overhead.

## Acceptance Criteria

- AC-1: The compiler and runtime expose three explicit MC/DC instrumentation states—statically disabled, statically enabled, and dynamically aspect-loaded—and focused IR/native evidence proves the statically disabled state emits no probes, dispatch, coverage state, registration, heap allocation, or dynamic-loader dependency on touched execution paths.
- AC-2: Statically enabled instrumentation records independent-condition influence for decisions containing short-circuit `and`/`or`, negation, nesting, repeated conditions, constants, early return, match/guard, and exceptional control flow without changing evaluation order, evaluation count, side effects, result, or exception behavior.
- AC-3: Dynamic aspect loading can activate and deactivate MC/DC collection without rebuilding the instrumentable program, performs no per-decision heap allocation after bounded initialization, uses bounded storage/capture, and adds only the measured minimal branch/dispatch overhead while inactive; configuration supports explicit buffer/capacity and reporting policy without raw environment reads in leaf modules.
- AC-4: MC/DC identity and aggregation are deterministic across interpreter and native modes, modules, parallel tasks, and repeated builds; concurrent recording is race-safe, has bounded memory, avoids global hot-path contention, and uses owner-result/deterministic parent-authoritative commit rather than shared mutable cross-domain state.
- AC-5: Normal mode and every stricter safety/criticality mode enforce 100% MC/DC over all producible in-scope decisions; below-normal behavior is explicitly specified. A deficient run exits nonzero with stable machine-readable and human-readable diagnostics identifying each missing condition pair.
- AC-6: Exclusion syntax is explicit and narrowly scoped, requires a non-empty reason plus stable scenario/decision identity, rejects blank, malformed, stale, overly broad, or reasonless exclusions, excludes only demonstrably non-producible conditions from the denominator, and reports all accepted exclusions separately rather than counting them as covered or skipped PASS results.
- AC-7: The existing `rt(hal)` tag selects and can concurrently exercise pure-Simple, C, and Rust providers for the same declared HAL operation without replacing or bypassing the pure owner; configuration selects provider sets, comparison policy, ordering, timeout, and mismatch handling while default behavior remains compatible.
- AC-8: RT/HAL differential comparison canonicalizes and compares operation inputs, outputs, errors, and observable I/O effects deterministically, detects disagreement without duplicating irreversible effects, distinguishes unsupported providers from mismatches, and emits bounded diagnostic evidence naming provider and operation.
- AC-9: Every RT/HAL interaction test is represented as a typed, bounded environment-access instruction separated from assertions; an environment executor performs each allowed interaction, returns a receipt, rejects undeclared or unsafe interaction, and permits deterministic fake/replay execution without direct environment/process calls in test leaf modules.
- AC-10: Unavailable hardware/host scenarios remain visible as `unsupported` or `blocked` with reason, prerequisite, owner, retained artifacts, and exact resume command; they are never silently omitted, converted to a generic skip, or used to claim full feature completion.
- AC-11: RT declarations default to mission-critical mode or stricter unless explicitly annotated otherwise. The migration stage emits one actionable warning for legacy implicit criticality, provides a documented escalation switch/timeline, and the later enforcement stage converts the same condition into a stable compile error without weakening explicitly declared modes.
- AC-12: RT hardening rejects unbounded allocation, blocking, recursion, dynamic dispatch, loader work, unbounded logging, and unbounded synchronization on mission-critical hot paths unless an existing capability contract explicitly proves them safe; diagnostics identify the violated operation and remediation, and real correctness/SPipe coverage exercises adjacent safe and unsafe cases.
- AC-13: For every touched hot path, the implementation review records algorithmic complexity first, then allocations/copies, data layout/locality, loop hoisting, dispatch, synchronization, and logging overhead. The same existing baseline and after-change workload reports wall time plus peak RSS/allocation evidence; static-off must be measurement-equivalent within the repository's declared noise threshold, and meaningful regressions are fixed or retained as concrete tracked bugs with measurements and unblock conditions.
- AC-14: Pure-Simple remains the semantic owner and implementation language for compiler/library/app behavior. C/Rust changes are allowed only at an already-delegated runtime/FFI boundary with evidence that pure Simple delegates correctly; no pure implementation is replaced by a foreign one.
- AC-15: Executable SSpec/SPipe scenarios trace every requirement, use real assertions and fail-fast scaffolds during construction, cover static-off/on/dynamic modes, denominator/exclusion failures, RT criticality warning/error staging, parallel provider parity/mismatch, bounded environment receipts, concurrency, and allocation/performance contracts; mirrored `doc/06_spec` manuals are generated by SPipe and readable as operator workflows.
- AC-16: Verification uses the pure-Simple self-hosted toolchain and the smallest documented target/provider/SCI projection with an admitted receipt; no Rust-seed/stub fallback is accepted. Each acceptance command runs once after convergence, no criterion is rechecked after a green result, and work stops after three distinct fix/verify cycles with remaining failures reported.
- AC-17: Knowledge is updated in the same coherent change: research, requirements, architecture, design, system-test plan, agent-task plan, and tracking records under `doc/`; reachable user/developer behavior under `doc/07_guide/`; feature and compiler/runtime/HAL layer expert skills under `doc/00_llm_process/`; concrete unresolved gaps under `doc/08_tracking/bug/`; and affected SPipe manuals plus `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`, and `.gemini/commands/` workflow instructions. Each unaffected surface is marked N/A with a concrete reason.
- AC-18: The final completion audit maps every AC to authoritative current-state source, executable evidence, measured performance/memory result, or retained external-host blocker; completion is prohibited while any AC is missing, indirect, contradicted, or merely planned.

## Scope Exclusions

- Replacing pure-Simple compiler, coverage, RT, or HAL owners with C or Rust.
- Treating unavailable physical hardware evidence as PASS or deleting its requirement.
- General compiler/runtime optimization unrelated to the touched MC/DC, aspect, RT criticality, environment-instruction, or `rt(hal)` paths.
- Release/version tagging unless separately requested after verification passes.

## Cooperative Review

- Sidecars: parallel agents may independently inventory MC/DC/aspect implementation, RT/HAL tag/provider comparison, environment-instruction/skip infrastructure, and performance/memory baselines; they must not edit the same files without explicit ownership transfer.
- Merge owner: primary Codex agent (`/root`).
- Final reviewer: primary normal/highest-capability Codex agent after sidecar findings and diffs are reconciled.
- Shared interfaces: `McdcMode`, `McdcDecisionId`, `McdcRecorder`, `McdcExclusion`, `RtHalProvider`, `RtHalComparison`, `EnvAccessInstruction`, and `EnvAccessReceipt` (final spellings may change only once during architecture review and must then be propagated consistently).
- Manual flow helpers: `step("configure MC/DC mode")`, `step("exercise independent conditions")`, `step("load dynamic MC/DC aspect")`, `step("compare RT/HAL providers")`, `step("execute environment instructions")`, `step("validate reasoned exclusions")`, and `step("enforce RT criticality")`.
- Setup/checker helpers: `setup_mcdc_fixture`, `setup_rt_hal_providers`, `setup_env_executor`, `check_mcdc_report`, `check_rt_hal_parity`, `check_env_receipt`, and `check_zero_overhead_evidence`.
- Fail-fast placeholders: executable scenarios use `assert(false)` or `fail(...)` until their real assertion and implementation exist; placeholder passes are forbidden.
- Generated-manual review owner: primary Codex agent, with one independent sidecar review of step/capture/helper clarity before final verification.

## Phase

verification-blocked-stage3-surface-freeze-segv

## Log

- dev: Created state file with 18 acceptance criteria (type: feature).
- research: Six parallel read-only lanes completed. Combined local/domain research
  and feature/NFR options were written; design waits for user selection.
- requirements: User selected feature C and NFR N2 (message: `c m2`, interpreted
  as N2). Final requirement artifacts created; architecture/design started.
- design: Architecture, detail design, system-test plan, and serialized ownership
  plan completed after three independent read-only design reviews. No production
  implementation or verification has run.
- implementation: Frozen Pure Simple MC/DC, RT/HAL, and environment-access
  contract models plus unit coverage were added. The first focused check could
  not start because the deployed Pure Simple runtime is absent and no admitted
  Stage 2 binary/receipts exist. Recorded the exact blocker under doc/08_tracking.
- recovery: Fixed missing bootstrap-only `dispatch_profile` module wiring. A
  one-job full bootstrap then reached Pure Simple Stage 2 and stayed CPU-active/
  memory-bounded, but was externally terminated with exit 143 after about 55
  minutes before publishing an admitted artifact. Identical retry is prohibited
  this session; incremental cache and progress evidence were preserved.
- hardening: Fixed invalid zero/negative physical-alignment division, changed
  QEMU mock register copying from repeated concatenation O(n^2) to one O(n) copy,
  enforced register widths, and deduplicated pending IRQ injection. These remain
  unverified pending the Pure Simple runtime.
- sync: Linear rebase onto current origin/main increased tracked files from
  117871 to 119106 without conflict or loss; unrelated deletions were protected
  and restored.
- recovery: Pure Simple Stage 2 is admitted with sanity/provenance receipts. A
  focused native smoke compiled and executed the common contracts. General
  check/test remains unavailable; Stage 3 reached HIR completion but did not
  publish an artifact.
- implementation: Replaced per-evaluation mask arrays with four inline words and
  added `McdcRecorder`, a preallocated owner-local fixed ring. Recording is O(1)
  with no capacity growth after creation; drop/overwrite saturation is explicit
  and saturating. Focused Stage 2 native smoke passed.
- implementation: Added explicit inline masking words so later masking MC/DC
  cannot infer don't-care conditions from coincidental outcomes. Added a bounded
  expected-O(E*C) unique-cause analyzer with open addressing and deterministic
  earliest-pair retention. Its Stage 2 smoke exposed native Boolean occupancy
  misreads; after three cycles the table was changed to integer occupancy and
  left pending the next-session verification per the hard iteration cap.
- implementation: Integer occupancy produced the correct two signatures. Pair
  selection still returned zero, so target/outcome dispatch was converted to a
  numeric four-state key and left pending the next focused run rather than
  looping.
- implementation: `CompilerConfig` now owns explicit off/on/dynamic MC/DC mode,
  1 MiB owner and 64 MiB global defaults, CLI/env selection, and bounded memory
  overrides. Dynamic mode does not enable the legacy always-on coverage flag;
  static off is the default. A native `.to_i64()` coercion returned pointer-like
  values, so bounds use the fail-closed decimal parser. Focused Stage 2 config
  smoke compiled and executed `compiler-mcdc-config-ok`.
- implementation alignment (unverified): MC/DC is now represented by HIR
  decision metadata and MIR `DecisionProbe`/`ConditionProbe` records. MIR
  lowering preserves short-circuit control flow, emits explicit evaluated,
  truth, and Boolean-derivative masking information, and expands admitted
  probes to static or dynamic Pure Simple runtime calls before backend
  translation. Backends and the interpreter fail closed if an unexpanded probe
  reaches them; static-off phase gates omit the route entirely.
- implementation alignment (unverified): the dynamic controller validates the
  aspect ABI/schema/readiness at a cold quiescent publication boundary, binds a
  preallocated owner capsule through TLS, and keeps the dormant decision path
  to a publication branch without catalog lookup or allocation. Static
  recording shares the same bounded capsule/recorder representation without
  dynamic dispatch.
- implementation alignment (unverified): the test runner now accepts bounded,
  framed `MCDC-EVIDENCE-v1` child transport, analyzes declared obligations,
  validates reasoned exclusions/omissions separately, and applies the
  assurance-sensitive exact-completion gate. No runner or gate check has been
  accepted yet.
- implementation alignment (unverified): `rt(hal)` metadata survives frontend
  and HIR lowering into a MIR boundary. Pure observations are compared through
  exact 256-bit canonical receipts in a bounded process task arena; C/Rust
  workers receive scalar encoded requests or replay receipts and cannot commit
  the original effect. Parent order is deterministic and timed cancellation is
  explicit.
- implementation alignment (unverified): typed environment plans now resolve
  repo-contained resources and pinned allowlisted tools before one bounded host
  execution, with typed rejection/blocked/timeout receipts. Scenario omissions
  require stable identity, reason, prerequisite, owner, evidence, and resume
  data and remain distinct from MC/DC denominator exclusions.
- implementation alignment (unverified): RT declarations retain profile/reason/
  bounds through AST and HIR registries. Transitive admission defaults implicit
  RT to critical, stages the warning/error policy, and checks allocation,
  blocking, recursion, dispatch, synchronization, logging, loader work, and
  declared bound manifests.
- implementation alignment (unverified): recoverable exception MIR gained a
  bounded thread-local frame ABI for POSIX ELF x86-64/AArch64/RV64 and explicit
  rejection elsewhere. C, LLVM-library, RV32, and unsupported object targets
  remain tracked gaps; source presence is not backend verification.
- evidence scaffolding (unverified): executable system specs, mirrored manuals,
  and pinned MC/DC/analyzer/RT-HAL performance fixtures and receipt scripts now
  exist. They deliberately reject missing timing, peak RSS, allocation, or
  optimizer evidence and must not be cited as PASS until executed by an
  admitted self-hosted runtime.
- remediation alignment (unverified): the compiler serializes proof-bound
  formal masking contexts for each Boolean leaf. The runner derives evidence
  only on the cold reporting path using memoized three-valued postfix evaluation;
  each context admits at most 64 sibling requirements (within the existing
  256-condition decision bound), and fingerprints bind it to the Boolean tree.
- remediation alignment (unverified): tagged RT/HAL returns now perform O(1)
  scalar/reference writes into fixed per-owner receipt rings (16 owners, 64
  receipts each). Hashing, process work, comparison, diagnostics, and final
  status occur after quiescence in the cold drain. An injected finalizer rejects
  undrained, saturated, timed-out, or mismatched evidence.
- remediation alignment (unverified): hosted hardware access uses a sealed typed
  probe registry capped at 64 adapters. Registration validates identity/schema/
  bounds; execution rejects undeclared, unavailable, duplicate, late, or
  over-bound probes, and adapters do not receive process capability.
- remediation alignment (unverified): native recoverable-unwind source lowering
  is present for POSIX ELF x86-64/AArch64/RV64. C translation, LLVM-library,
  Mach-O, RV32, and other unsupported combinations remain stable errors.
- remediation alignment (unverified): real test-only C and Rust comparators now
  implement `rthal-scalar-v1`. A typed plan builds them with pinned compiler
  identities, hashes the outputs, and admits them to the exact process arena;
  Pure Simple remains the effect and semantic owner.
- verification recovery: fixed misplaced recoverable-unwind borrow definitions
  and an erased-receiver `batch.find` mis-lowering to `rt_string_find`. A fresh
  Stage 2 then passed native build, frontend/positional-entry sanity, independent
  struct-receiver/runtime proof, and admission. The admitted one-thread Stage 3
  loaded 992 surfaces but SIGSEGV'd in `surface_freeze` at about 10.3 GiB RSS.
  The three-cycle cap is exhausted; the release-blocking evidence and unblock
  condition are recorded in
  `doc/08_tracking/bug/stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25.md`.
- doc/wiki refactor: refreshed the MC/DC/RT/HAL guide, system-test plan, V3
  provider/environment manuals, canonical typed-exit design, SPipe skill, and
  feature-expert wiki. Runtime/docgen evidence remains unverified pending an
  admitted self-hosted executable; no blocked row was converted to a skip.
