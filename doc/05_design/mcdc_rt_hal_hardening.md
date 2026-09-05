<!-- codex-design -->
# MC/DC, RT, and HAL Hardening Detail Design

## Core records

- `McdcMode`: `StaticOff | StaticOn | DynamicAspect`.
- `McdcPolicy`: masking policy, unique-cause retention, condition/nesting bounds,
  owner/global bytes and overflow policy.
- `McdcDecisionId`: stable semantic ID plus compact build-local runtime ID.
- `McdcEvaluation`: fixed decision/owner/sequence/outcome and evaluated/true masks;
  default maximum 256 occurrences. Larger decisions require an explicit bound.
- `McdcRecorder`: owner-bound fixed ring port with saturating counters.
- `McdcExclusion`: semantic ID, optional occurrence, reason, reviewer, review ID,
  expiry/version. Blank, stale, duplicate or broad records fail.

MIR uses `DecisionBegin`, post-evaluation `ConditionProbe`, and `DecisionEnd`.
Throws abort the bounded slot. Metadata is sorted and frozen before build caching.

## Provider contracts

`RtHalProvider` exposes identity/capabilities and query/replay only.
`RtHalComparison` contains provider order, bounded worker/queue counts, deadline,
output cap and require-all policy. Canonical outcome is Value, Error, or Blocked;
observable effects are ordered typed trace entries plus hashes. Custom providers
must pass ABI/schema/capability admission. Foreign-only configuration is invalid.

## Environment contracts

`EnvAccessInstruction` is a closed set: bounded env read, host identity, bounded
repo-relative file read, allowlisted process invocation, or hardware probe.
`EnvAccessReceipt` includes plan/index, Executed/Blocked/Unsupported/Rejected/
TimedOut status, bounded output hashes, truncation counts, reason, prerequisite,
owner, artifacts and exact resume command. Fake/replay implements the same port.

## Algorithms and safety

- Recorder: O(1) single-owner publish; consumer drains after join/generation fence.
- Analyzer: expected O(E*C) bounded open-addressed signature tables; verify full
  masks after hash matches and retain earliest deterministic pair.
- Parallel HAL: immutable request copy/frozen share to bounded child workers;
  child-created result envelopes; configured-order parent validation/commit.
- Effectful HAL: Pure executes once; comparators replay without effect capability.
- Dynamic activation: safe-point generation switch; never patch active RT code.
- Invalid config/ABI/metadata/exclusion fails before executable emission. Buffer
  saturation makes normal+ evidence incomplete. No blocked/error state becomes PASS.

## Performance design

Static off creates no probe route. Static-on probes contain constants, one hoisted
owner handle and a fixed record write. Use SoA metadata for report scans and compact
fixed events for locality; no source strings in events. Thresholds are integer
basis points: static-on time/RSS <=500 bp, dormant <=100 bp, enabled <=1000 bp.
Measure identical fixture/build inputs, peak RSS, allocations, saturation and
correctness; optimizer receipts cover every touched `.spl` hot path.

## Compatibility

Existing coverage APIs remain until native parity is demonstrated. The rewrite is
deprecated, not silently changed. Existing explicit RT profiles remain valid.
Pure Simple is never replaced; foreign code stays behind already delegated ABI
surfaces. No UI is introduced, so TUI/GUI design is not applicable.

## Source-realized interfaces (unverified)

- HIR decisions carry semantic identity, condition count, masking policy, and
  fixed projection words. MIR carries `DecisionProbe` and `ConditionProbe`; the
  latter identifies ordinal, evaluated result, and mask range/polarity.
- MIR lowering owns an active decision/token stack. It emits begin, evaluated
  condition, derivative mask, end, and abort calls without reevaluating user
  expressions. Return/throw/unwind exits abort active observations.
- `McdcDynamicAspect` owns fixed in-flight word arrays and an optional fixed
  recorder. `McdcProbeRegistry` owns bounded owner slots; `dynamic_probe` owns
  catalog publication/generation and TLS slot binding; `static_probe` is the
  direct-call facade.
- `McdcConditionPolicy` supplies required policy and four projection words.
  `McdcCoverageClassification` distinguishes unique-cause, masking, insufficient
  evaluations, missing projection metadata, and uncovered results.
- The runner transport is a sentinel-framed, versioned text protocol with a
  64-MiB/one-million-row ceiling. Obligation, evaluation, exclusion, and
  saturation records are parsed into typed values before enforcement.
- `McdcCoverageGateReport` is the sole exact-completion decision. Machine and
  human reports derive from the same bounded diagnostic rows.
- `RtHalExactRequest`, `RtHalCanonicalReceipt`, and `RtHalExactJoin` form the
  comparison ABI. `RtHalProcessTaskArena` preallocates at most 16 adapters and
  256 task slots; opaque handles include slot generations to reject stale joins.
- `rt_hal_execute_registered_exact` is the public tagged entry to that ABI. It
  accepts already-observed Pure receipts and schedules only registered C/Rust
  adapters; callback-shaped foreign execution fails closed. Pure-only legacy
  calls remain synchronous and are admitted through the same queue/output byte
  bounds without using the runtime pool.
- `EnvAccessCapability` separates common validation/receipt construction from
  the app-owned host implementation. Tool paths require declared identity hashes
  and repo files require canonical containment.
- `ScenarioOmissionValidation` validates reasoned skips/blocked scenarios and
  can derive an MC/DC exclusion only when stable decision identity and review
  metadata are present.

## Recoverable unwind contract and limits

Runtime exception state is thread-local and bounded; no heap allocation occurs
while pushing, throwing, capturing, popping, or resuming a frame. MIR interpreter
semantics are the reference. Native x86-64/AArch64/RV64 and textual LLVM source
paths implement the selected POSIX ELF ABI; unsupported paths emit stable errors.
The C backend, LLVM library emitter, RV32, non-POSIX/non-ELF targets, and complete
structural catch identities remain intentionally fail-closed and unverified.

## Evidence design now present

System specs cover mode/semantics, exclusions/gating, owner-local recording,
RT/HAL differential behavior, environment receipts, and RT criticality. The perf
directory contains one identical MC/DC decision loop, analyzer scaling fixture,
RT/HAL fixture, integer thresholds, optimizer input list, and scripts intended
to capture wall time, peak RSS, allocation and optimizer receipts. A receipt
with a missing field is invalid. No source fixture, generated manual, or script
is itself evidence of meeting a threshold; all results remain unverified.

## Latest remediation details (unverified)

- `CompilerMcdcTargetContext` carries ordered sibling requirements, reasons,
  proof/context fingerprints, and leaf identities. Requirements serialize as
  bounded postfix Boolean programs.
- `RunnerMcdcContextPlan` validates at most 64 requirements per target and cold-
  derives context evidence with a per-row program cache. Unknown short-circuited
  inputs are masked; contrary observed sibling outcomes reject the row.
- `rt_hal_boundary_dispatch` performs a bounds check and writes preallocated SoA
  ring columns (16 owners × 64 rows). `rt_hal_boundary_drain_owner` performs
  digest/process comparison after quiescence, and the owner finalizer prevents
  success while evidence is undrained or failed.
- `HostHardwareProbeAdapter` supplies typed availability/execution ports.
  Registration validates and deduplicates at startup, caps at 64, and seals on
  first plan execution; schema and bounds are checked again before invocation.
- `test/fixtures/rt_hal_external/` contains C/Rust scalar providers, a pinned
  typed build/provider plan, and setup/compare driver. Malformed input exits
  without a receipt; foreign children never own the original effect.
- Native unwind is admitted in design only for POSIX ELF x86-64/AArch64/RV64.
  C, LLVM-library, Mach-O, and RV32 remain fail-closed obligations.
