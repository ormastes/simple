# Claude Full AutoUpdater Utils

> Checks the autoUpdater class and exported result/config surface required by strict parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AutoUpdater Utils

Checks the autoUpdater class and exported result/config surface required by strict parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the autoUpdater class and exported result/config surface required by strict parity.

## Scenarios

### Claude full autoUpdater utils

#### should expose AutoUpdaterError

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose AutoUpdaterError
   - Expected: err.name equals `AutoUpdaterError`
   - Expected: err.message equals `install failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose AutoUpdaterError")
val err = AutoUpdaterError.new("install failed")
expect(err.name).to_equal("AutoUpdaterError")
expect(err.message).to_equal("install failed")
```

</details>

#### should expose result config and status surface

- should expose result config and status surface
   - Expected: result.version equals `1.2.3`
   - Expected: result.status equals `success`
   - Expected: result.notifications[0] equals `updated`
   - Expected: config.external equals `2.0.0`
   - Expected: config.antMessage equals `ant blocked`
   - Expected: isInstallStatus("success") is true
   - Expected: isInstallStatus("pending") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose result config and status surface")
val result = AutoUpdaterResult.new("1.2.3", "success", ["updated"])
expect(result.version).to_equal("1.2.3")
expect(result.status).to_equal("success")
expect(result.notifications[0]).to_equal("updated")
val config = MaxVersionConfig.new("2.0.0", "3.0.0", "external blocked", "ant blocked")
expect(config.external).to_equal("2.0.0")
expect(config.antMessage).to_equal("ant blocked")
expect(isInstallStatus("success")).to_equal(true)
expect(isInstallStatus("pending")).to_equal(false)
```

</details>

#### should expose constants and source size

- should expose constants and source size
   - Expected: autoUpdaterSourceLinesModeled() equals `561`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose constants and source size")
expect(gcsBucketUrl()).to_contain("claude-code-releases")
expect(autoUpdaterSourceLinesModeled()).to_equal(561)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6590b5334240906d4e1cefd2007cc7e3d8bed065a910e27b34ea8c63ae898ac7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6590b5334240906d4e1cefd2007cc7e3d8bed065a910e27b34ea8c63ae898ac7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6590b5334240906d4e1cefd2007cc7e3d8bed065a910e27b34ea8c63ae898ac7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/autoUpdater_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/autoUpdater_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/autoUpdater_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose AutoUpdaterError' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose AutoUpdaterError' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose result config and status surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose result config and status surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose constants and source size' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose constants and source size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
