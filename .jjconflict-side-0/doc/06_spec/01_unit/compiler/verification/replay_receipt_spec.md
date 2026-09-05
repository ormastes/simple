# Replay Receipt Specification

> Tests covering FV2 fresh and independent proof replay receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Receipt Specification

## Scenarios

### FV2 fresh and independent proof replay receipts

#### requires two distinct checker classes over one exact artifact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires two distinct checker classes over one exact artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires two distinct checker classes over one exact artifact")
val closure = close_independent_replay_v1(
    replay_receipt(ReplayCheckerClassV1.FreshLeanKernel),
    replay_receipt(ReplayCheckerClassV1.IndependentKernel))
expect(closure.accepted).to_be(true)
expect(closure.hash() == "").to_be(false)
```

</details>

#### does not mislabel two Lean-kernel replays as independent

- does not mislabel two Lean-kernel replays as independent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mislabel two Lean-kernel replays as independent")
val closure = close_independent_replay_v1(
    replay_receipt(ReplayCheckerClassV1.FreshLeanKernel),
    replay_receipt(ReplayCheckerClassV1.FreshLeanKernel))
expect(closure.accepted).to_be(false)
expect(closure.diagnostic).to_contain("INDEPENDENT-CLASS")
```

</details>

#### rejects relabelled checker binaries and malformed accepted identities

- rejects relabelled checker binaries and malformed accepted identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects relabelled checker binaries and malformed accepted identities")
val fresh = replay_receipt(ReplayCheckerClassV1.FreshLeanKernel)
val relabelled = ReplayCheckerReceiptV1(
    "ReplayCheckerReceipt-v1", ReplayCheckerClassV1.IndependentKernel,
    "nanoda", "pinned-version", fresh.binary_hash,
    fresh.module_name, fresh.declaration_root, fresh.artifact_hash,
    fresh.command_policy_hash, fresh.output_hash,
    ReplayOutcomeV1.Accepted, "")
val closure = close_independent_replay_v1(fresh, relabelled)
expect(closure.accepted).to_be(false)
expect(closure.diagnostic).to_contain("INDEPENDENCE")
val malformed = ReplayCheckerReceiptV1(
    "ReplayCheckerReceipt-v1", ReplayCheckerClassV1.FreshLeanKernel,
    "leanchecker", "pinned-version", "not-a-hash", "Verified.Module",
    "Verified.Module.root", sha256_text("artifact"),
    sha256_text("policy"), sha256_text("output"),
    ReplayOutcomeV1.Accepted, "")
expect(malformed.accepted()).to_be(false)
```

</details>

#### rejects a caller-invented checker family despite a valid-looking hash

- rejects a caller-invented checker family despite a valid-looking hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a caller-invented checker family despite a valid-looking hash")
val forged = ReplayCheckerReceiptV1(
    "ReplayCheckerReceipt-v1", ReplayCheckerClassV1.IndependentKernel,
    "unreviewed-checker", "pinned-version",
    sha256_text("unreviewed-binary"), "Verified.Module",
    "Verified.Module.root", sha256_text("artifact"),
    sha256_text("policy"), sha256_text("output"),
    ReplayOutcomeV1.Accepted, "")
expect(forged.accepted()).to_be(false)
```

</details>

#### rejects declaration-root drift inside one module and artifact

- rejects declaration-root drift inside one module and artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects declaration-root drift inside one module and artifact")
val fresh = replay_receipt(ReplayCheckerClassV1.FreshLeanKernel)
val independent = ReplayCheckerReceiptV1(
    "ReplayCheckerReceipt-v1", ReplayCheckerClassV1.IndependentKernel,
    "nanoda", "pinned-version", sha256_text("independent-kernel-binary"), "Verified.Module",
    "Verified.Module.weaker_root", sha256_text("artifact"), sha256_text("command-policy"),
    sha256_text("output"), ReplayOutcomeV1.Accepted, "")
val closure = close_independent_replay_v1(fresh, independent)
expect(closure.accepted).to_be(false)
expect(closure.diagnostic).to_contain("REPLAY-ROOT")
```

</details>

#### rejects checker disagreement artifact drift and lost output

- rejects checker disagreement artifact drift and lost output


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects checker disagreement artifact drift and lost output")
val rejected = close_independent_replay_v1(
    replay_receipt(ReplayCheckerClassV1.FreshLeanKernel),
    replay_receipt(ReplayCheckerClassV1.IndependentKernel,
        sha256_text("artifact"), ReplayOutcomeV1.Rejected))
expect(rejected.accepted).to_be(false)
expect(rejected.diagnostic).to_contain("INDEPENDENT")

val drift = close_independent_replay_v1(
    replay_receipt(ReplayCheckerClassV1.FreshLeanKernel, sha256_text("first")),
    replay_receipt(ReplayCheckerClassV1.IndependentKernel, sha256_text("second")))
expect(drift.accepted).to_be(false)
expect(drift.diagnostic).to_contain("ARTIFACT")

val lost = replay_receipt(
    ReplayCheckerClassV1.FreshLeanKernel, sha256_text("artifact"),
    ReplayOutcomeV1.MissingOutput, "")
expect(lost.accepted()).to_be(false)
```

</details>

#### rejects command injection and incomplete runner identities before execution

- rejects command injection and incomplete runner identities before execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects command injection and incomplete runner identities before execution")
expect(replay_module_name_is_safe_v1("Verified.Module_1")).to_be(true)
expect(replay_module_name_is_safe_v1("Verified;touch.bad")).to_be(false)
expect(replay_module_name_is_safe_v1("../Verified")).to_be(false)
expect(replay_module_name_is_safe_v1("Verified..root")).to_be(false)
expect(replay_module_name_is_safe_v1("1Verified.root")).to_be(false)

val invalid = ReplayRunnerConfigV1(
    "/tmp/project", "Verified.Module", "Verified.root", "/tmp/module.olean", sha256_text("artifact"),
    "/bin/launcher", "/bin/tool",
    "nanoda-adapter", "", 1000)
expect(replay_runner_config_error_v1(invalid)).to_contain("IDENTITY")
```

</details>

#### rejects caller-selected fresh replay tools without canonical authority

- rejects caller-selected fresh replay tools without canonical authority
   - Expected: receipt.outcome equals `ReplayOutcomeV1.ToolFailure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects caller-selected fresh replay tools without canonical authority")
val caller_selected = ReplayRunnerConfigV1(
    "/tmp/project", "Verified.Module", "Verified.root",
    "/tmp/module.olean", sha256_text("artifact"), "/bin/echo",
    "/bin/echo", "leanchecker", "caller-version", 1000)
val receipt = run_fresh_leanchecker_v1(caller_selected)
expect(receipt.accepted()).to_be(false)
expect(receipt.outcome).to_equal(ReplayOutcomeV1.ToolFailure)
expect(receipt.diagnostic).to_contain("REPLAY-AUTHORITY")
expect(receipt.diagnostic).to_contain("Lake and leanchecker")
```

</details>

#### rejects a self-consistent caller adapter without canonical authority

- rejects a self-consistent caller adapter without canonical authority
   - Expected: receipt.outcome equals `ReplayOutcomeV1.ToolFailure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a self-consistent caller adapter without canonical authority")
val caller_selected = ReplayRunnerConfigV1(
    "/tmp/project", "Verified.Module", "Verified.root",
    "/tmp/module.olean", sha256_text("artifact"), "/bin/echo",
    "/bin/echo", "nanoda-adapter", "caller-version", 1000)
val receipt = run_independent_replay_adapter_v1(caller_selected)
expect(receipt.accepted()).to_be(false)
expect(receipt.outcome).to_equal(ReplayOutcomeV1.ToolFailure)
expect(receipt.diagnostic).to_contain("REPLAY-AUTHORITY")
expect(receipt.diagnostic).to_contain("adapter, lean4export, and nanoda")
```

</details>

#### binds both the launcher and checker binary into replay identity

- binds both the launcher and checker binary into replay identity
   - Expected: replay_executable_identity_hash_v1("", checker) equals ``
   - Expected: replay_executable_identity_hash_v1("lake-a", checker) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds both the launcher and checker binary into replay identity")
val lake = sha256_text("lake-a")
val checker = sha256_text("leanchecker-a")
val baseline = replay_executable_identity_hash_v1(lake, checker)
expect(baseline == "").to_be(false)
expect(replay_executable_identity_hash_v1(sha256_text("lake-b"), checker) == baseline).to_be(false)
expect(replay_executable_identity_hash_v1(lake, sha256_text("leanchecker-b")) == baseline).to_be(false)
expect(replay_executable_identity_hash_v1("", checker)).to_equal("")
expect(replay_executable_identity_hash_v1("lake-a", checker)).to_equal("")
```

</details>

#### permits synthesized silence evidence only for the fresh checker class

- permits synthesized silence evidence only for the fresh checker class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("permits synthesized silence evidence only for the fresh checker class")
val source = file_read("src/compiler/90.tools/verify/replay_runner.spl")
expect(source).to_contain("FV2-FRESH-LEAN-KERNEL-ACCEPTED")
expect(source).to_contain("successful independent checker emitted no retained evidence")
```

</details>

#### does not hash a hand-assembled closure with a forged schema

- does not hash a hand-assembled closure with a forged schema
   - Expected: forged.hash() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hash a hand-assembled closure with a forged schema")
val forged = IndependentReplayClosureV1(
    "forged", "fresh", "independent", "artifact", true, "")
expect(forged.hash()).to_equal("")
```

</details>

#### does not hash a schema-shaped closure with forged receipt identities

- does not hash a schema-shaped closure with forged receipt identities
   - Expected: forged.hash() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hash a schema-shaped closure with forged receipt identities")
val forged = IndependentReplayClosureV1(
    "IndependentReplayClosure-v1", "fresh", "independent",
    "artifact", true, "")
expect(forged.hash()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/replay_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 fresh and independent proof replay receipts.
- FV2 fresh and independent proof replay receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f2310a472a789ad074f67837d3d8643d69610c2c0eb7c797863e5dd33cd8642`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f2310a472a789ad074f67837d3d8643d69610c2c0eb7c797863e5dd33cd8642`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f2310a472a789ad074f67837d3d8643d69610c2c0eb7c797863e5dd33cd8642`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/verification/replay_receipt_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/replay_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/replay_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/replay_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/replay_receipt_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires two distinct checker classes over one exact artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/replay_receipt_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not mislabel two Lean-kernel replays as independent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/replay_receipt_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects relabelled checker binaries and malformed accepted identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
