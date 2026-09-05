# scv_checkpoint_spec

> Purpose: This spec proves `scv checkpoint` writes an immutable content-addressed

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_checkpoint_spec

Purpose: This spec proves `scv checkpoint` writes an immutable content-addressed

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_checkpoint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv checkpoint` writes an immutable content-addressed
checkpoint of the must-back-up repository state and that `scv checkpoint verify`
recomputes and detects tampering (stabilization report §2).
Audience: Maintainers of the SCV stabilization tooling.

## Scenarios

### scv checkpoint

#### creates a content-addressed checkpoint that verifies clean

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a content-addressed checkpoint that verifies clean
- Create a checkpoint and verify it
- Verify the checkpoint id and verification verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates a content-addressed checkpoint that verifies clean")
step("Create a checkpoint and verify it")
var lines = _prelude("clean")
lines.push("OUT=$(scv checkpoint)")
lines.push("printf '%s\\n' \"$OUT\"")
lines.push("ID=$(printf '%s\\n' \"$OUT\" | awk '/^checkpoint /{print $2}')")
lines.push("test -f \".scv/checkpoints/$ID/manifest.sdn\"")
lines.push("scv checkpoint verify \"$ID\"")
val out = _run(lines)
step("Verify the checkpoint id and verification verdict")
expect(out).to_contain("checkpoint checkpoint_")
expect(out).to_contain("OK checkpoint checkpoint_")
expect(out).to_contain("exit=0")
```

</details>

#### excludes rebuildable parser state from the checkpoint

- excludes rebuildable parser state from the checkpoint
- Checkpoint and inspect the manifest contents
- Verify must-back-up data is present and rebuildable data absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("excludes rebuildable parser state from the checkpoint")
step("Checkpoint and inspect the manifest contents")
var lines = _prelude("scope")
lines.push("scv parse-index >/dev/null 2>&1 || true")
lines.push("OUT=$(scv checkpoint)")
lines.push("ID=$(printf '%s\\n' \"$OUT\" | awk '/^checkpoint /{print $2}')")
lines.push("M=\".scv/checkpoints/$ID/manifest.sdn\"")
lines.push("printf 'has_head=%s\\n' \"$(grep -c ' HEAD_OP$' \"$M\")\"")
lines.push("printf 'has_ops=%s\\n' \"$([ \"$(grep -c ' objects/operations/' \"$M\")\" -gt 0 ] && echo yes || echo no)\"")
lines.push("printf 'has_changes=%s\\n' \"$([ \"$(grep -c ' objects/changes/' \"$M\")\" -gt 0 ] && echo yes || echo no)\"")
lines.push("printf 'has_chunks=%s\\n' \"$([ \"$(grep -c ' objects/chunks/' \"$M\")\" -gt 0 ] && echo yes || echo no)\"")
lines.push("printf 'has_parser=%s\\n' \"$(grep -c 'parser' \"$M\")\"")
lines.push("printf 'has_syntax=%s\\n' \"$(grep -c ' objects/syntax/' \"$M\")\"")
val out = _run(lines)
step("Verify must-back-up data is present and rebuildable data absent")
expect(out).to_contain("has_head=1")
expect(out).to_contain("has_ops=yes")
expect(out).to_contain("has_changes=yes")
expect(out).to_contain("has_chunks=yes")
expect(out).to_contain("has_parser=0")
expect(out).to_contain("has_syntax=0")
expect(out).to_contain("exit=0")
```

</details>

#### fails verification when a checkpointed file is tampered with

- fails verification when a checkpointed file is tampered with
- Corrupt one checkpointed object and re-verify
- Verify tampering is reported and the exit code is non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails verification when a checkpointed file is tampered with")
step("Corrupt one checkpointed object and re-verify")
var lines = _prelude("tamper")
lines.push("OUT=$(scv checkpoint)")
lines.push("ID=$(printf '%s\\n' \"$OUT\" | awk '/^checkpoint /{print $2}')")
lines.push("F=$(find \".scv/checkpoints/$ID/data/objects/chunks\" -type f | head -1)")
lines.push("printf 'tampered' >> \"$F\"")
lines.push("set +e")
lines.push("scv checkpoint verify \"$ID\"")
lines.push("printf 'verify_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify tampering is reported and the exit code is non-zero")
expect(out).to_contain("ERROR checkpoint verify failed")
expect(out).to_contain("verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects verification of a missing checkpoint id

- rejects verification of a missing checkpoint id
- Verify a checkpoint id that does not exist
- Verify the missing checkpoint is a nothing-was-checked error


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects verification of a missing checkpoint id")
step("Verify a checkpoint id that does not exist")
var lines = _prelude("missing")
lines.push("set +e")
lines.push("scv checkpoint verify checkpoint_does_not_exist")
lines.push("printf 'verify_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify the missing checkpoint is a nothing-was-checked error")
expect(out).to_contain("ERROR — nothing was checked")
expect(out).to_contain("verify_code=2")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-CHECKPOINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7952c502b96d31893244ff9c6fd981e037456c2ef457903f2816eaccd256c99e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7952c502b96d31893244ff9c6fd981e037456c2ef457903f2816eaccd256c99e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7952c502b96d31893244ff9c6fd981e037456c2ef457903f2816eaccd256c99e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_checkpoint_spec.spl
mirror: doc/06_spec/integration/app/scv_checkpoint_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_checkpoint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_checkpoint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_checkpoint_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_checkpoint_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a content-addressed checkpoint that verifies clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_checkpoint_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes rebuildable parser state from the checkpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_checkpoint_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails verification when a checkpointed file is tampered with' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
