# Claude Full sandbox UI utils

> Pure Simple coverage for sandbox violation tag cleanup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full sandbox UI utils

Pure Simple coverage for sandbox violation tag cleanup.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for sandbox violation tag cleanup.

## Scenarios

### Claude full sandbox UI utils

#### leaves text without sandbox violation tags unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leaves text without sandbox violation tags unchanged
- Check no-op text
   - Expected: removeSandboxViolationTags("plain error") equals `plain error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves text without sandbox violation tags unchanged")
step("Check no-op text")
expect(removeSandboxViolationTags("plain error")).to_equal("plain error")
```

</details>

#### removes one sandbox violation block

- removes one sandbox violation block
- Check single block cleanup
   - Expected: removeSandboxViolationTags("before <sandbox_violations>secret</sandbox_violations> after") equals `before  after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes one sandbox violation block")
step("Check single block cleanup")
expect(removeSandboxViolationTags("before <sandbox_violations>secret</sandbox_violations> after")).to_equal("before  after")
```

</details>

#### removes multiline and repeated sandbox violation blocks

- removes multiline and repeated sandbox violation blocks
- Check global multiline cleanup
   - Expected: removeSandboxViolationTags(input) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes multiline and repeated sandbox violation blocks")
step("Check global multiline cleanup")
val input = "a<sandbox_violations>one\ntwo</sandbox_violations>b<sandbox_violations>x</sandbox_violations>c"
expect(removeSandboxViolationTags(input)).to_equal("abc")
```

</details>

#### leaves an unclosed trailing sandbox violation block unchanged

- leaves an unclosed trailing sandbox violation block unchanged
- Check regex-compatible malformed trailing block
   - Expected: removeSandboxViolationTags("visible <sandbox_violations>hidden") equals `visible <sandbox_violations>hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves an unclosed trailing sandbox violation block unchanged")
step("Check regex-compatible malformed trailing block")
expect(removeSandboxViolationTags("visible <sandbox_violations>hidden")).to_equal("visible <sandbox_violations>hidden")
```

</details>

#### removes adjacent blocks without adding separators

- removes adjacent blocks without adding separators
- Check adjacent cleanup
   - Expected: removeSandboxViolationTags("pre<sandbox_violations>\nfirst\n</sandbox_violations>mid<sandbox_violations>\nsecond\n</sandbox_violations>post") equals `premidpost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes adjacent blocks without adding separators")
step("Check adjacent cleanup")
expect(removeSandboxViolationTags("pre<sandbox_violations>\nfirst\n</sandbox_violations>mid<sandbox_violations>\nsecond\n</sandbox_violations>post")).to_equal("premidpost")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `2ffd12462617daaa23051bdb9ba1cac6432738d9d0d12a278a64ab65bee6b132`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ffd12462617daaa23051bdb9ba1cac6432738d9d0d12a278a64ab65bee6b132`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ffd12462617daaa23051bdb9ba1cac6432738d9d0d12a278a64ab65bee6b132`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves text without sandbox violation tags unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes one sandbox violation block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/sandbox/sandbox_ui_utils_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes multiline and repeated sandbox violation blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
