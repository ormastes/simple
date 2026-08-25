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
