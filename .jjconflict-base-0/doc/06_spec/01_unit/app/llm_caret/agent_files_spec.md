# Agent Files Specification

> Tests covering LLM Caret agent file snapshots.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Files Specification

## Scenarios

### LLM Caret agent file snapshots

#### skips missing and empty paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skips missing and empty paths
   - Expected: snap.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("skips missing and empty paths")
val snap = snapshot_agent_files("agent-1", ["", "/nonexistent/path/xyz.spl"])
expect(snap.len()).to_equal(0)
```

</details>

#### detects a changed fingerprint between snapshots

- detects a changed fingerprint between snapshots
   - Expected: changes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects a changed fingerprint between snapshots")
val before = [AgentFileFingerprint(agent_id: "a", path: "f.spl", fingerprint: "hash1")]
val after = [AgentFileFingerprint(agent_id: "a", path: "f.spl", fingerprint: "hash2")]
val changes = detect_agent_file_changes(before, after)
expect(changes.len()).to_equal(1)
expect(changes[0].changed_files).to_contain("f.spl")
```

</details>

#### reports no change for identical fingerprints

- reports no change for identical fingerprints
   - Expected: changed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports no change for identical fingerprints")
val fp = [AgentFileFingerprint(agent_id: "a", path: "f.spl", fingerprint: "hash1")]
val changes = detect_agent_file_changes(fp, fp)
var changed = 0
for c in changes:
    changed = changed + c.changed_files.len()
expect(changed).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_files_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret agent file snapshots.
- LLM Caret agent file snapshots

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `393683f5407199a14695e9af4c055954d31496d451b9d5f3466fb9677f311e55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `393683f5407199a14695e9af4c055954d31496d451b9d5f3466fb9677f311e55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `393683f5407199a14695e9af4c055954d31496d451b9d5f3466fb9677f311e55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/llm_caret/agent_files_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/agent_files_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/agent_files_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/agent_files_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/agent_files_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/agent_files_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips missing and empty paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_files_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a changed fingerprint between snapshots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_files_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no change for identical fingerprints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
