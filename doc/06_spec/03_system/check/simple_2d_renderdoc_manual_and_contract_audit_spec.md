# Simple 2D RenderDoc Manual and Contract Audit

> Keeps executable modern SSpec, generated manuals, guides, cooperative review,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D RenderDoc Manual and Contract Audit

Keeps executable modern SSpec, generated manuals, guides, cooperative review,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps executable modern SSpec, generated manuals, guides, cooperative review,
and source-layout contracts synchronized.

## Scenarios

### Simple 2D RenderDoc documentation contract

#### mirrors every executable scenario into an operator manual

- mirrors every executable scenario into an operator manual
   - Exec capture: after_step
- Inspect all backend-equivalence spec and manual pairs
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: SPECS.len() equals `MANUALS.len()`
   - Expected: SPECS.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mirrors every executable scenario into an operator manual")
step("Inspect all backend-equivalence spec and manual pairs")
expect(SPECS.len()).to_equal(MANUALS.len())
expect(SPECS.len()).to_equal(13)
var index = 0
while index < SPECS.len():
    expect(file_exists(SPECS[index])).to_be(true)
    expect(file_exists(MANUALS[index])).to_be(true)
    expect(file_read(MANUALS[index]).len()).to_be_greater_than(0)
    val legacy = MANUALS[index].replace("doc/06_spec/", "doc/06_spec/test/")
    expect(file_exists(legacy)).to_be(true)
    expect(file_read(legacy).len()).to_be_greater_than(0)
    index = index + 1
```

</details>

#### keeps modern steps requirements direct matchers and no fail placeholders

- keeps modern steps requirements direct matchers and no fail placeholders
   - Exec capture: after_step
- Audit scenario source quality
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: source contains `"expect(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps modern steps requirements direct matchers and no fail placeholders")
step("Audit scenario source quality")
for path in SPECS:
    val source = file_read(path)
    expect(source).to_contain("# @req")
    expect(source).to_contain("step(")
    expect(source).to_contain("expect(")
    if path != "test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl":
        expect(source.contains("pass_todo")).to_be(false)
        expect(source.contains("expect(true).to_equal(true)")).to_be(false)
        expect(source.contains("pending_")).to_be(false)
```

</details>

<details>
<summary>Advanced: rejects executable specs under the generated manual tree</summary>

#### rejects executable specs under the generated manual tree

- rejects executable specs under the generated manual tree
   - Exec capture: after_step
- Scan doc/06_spec for executable Simple files
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: code equals `0`
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects executable specs under the generated manual tree")
step("Scan doc/06_spec for executable Simple files")
val (out, _err, code) = process_run(
    "/bin/sh", ["-c", "find doc/06_spec -name '*_spec.spl' -print"])
expect(code).to_equal(0)
expect(out).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: requires sidecar merge and highest-capability review ownership</summary>

#### requires sidecar merge and highest-capability review ownership

- requires sidecar merge and highest-capability review ownership
   - Exec capture: after_step
- Inspect cooperative review completion
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires sidecar merge and highest-capability review ownership")
step("Inspect cooperative review completion")
val plan = file_read(
    "doc/03_plan/agent_tasks/simple_2d_renderdoc_backend_equivalence.md")
expect(plan).to_contain("Merge owner: primary Codex `/root`")
expect(plan).to_contain("Final reviewer: highest available normal Codex")
expect(plan).to_contain("Generated-manual review owner: primary Codex")
expect(plan).to_contain("Sidecars were read-only design auditors")
```

</details>


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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed21af16f464d78129b9f338af765a882010c7ec87f84fafd36ef31e35c57b8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed21af16f464d78129b9f338af765a882010c7ec87f84fafd36ef31e35c57b8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed21af16f464d78129b9f338af765a882010c7ec87f84fafd36ef31e35c57b8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl
mirror: doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=30
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mirrors every executable scenario into an operator manual' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps modern steps requirements direct matchers and no fail placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects executable specs under the generated manual tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
