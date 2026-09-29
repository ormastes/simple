# Claude Full bundled mode

> Pure Simple coverage for Bun runtime detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full bundled mode

Pure Simple coverage for Bun runtime detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bundled_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for Bun runtime detection.

## Scenarios

### Claude full bundled mode

#### detects Bun from version availability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects Bun from version availability
- Check Bun version marker
   - Expected: isRunningWithBun(true) is true
   - Expected: isRunningWithBun(false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Bun from version availability")
step("Check Bun version marker")
expect(isRunningWithBun(true)).to_equal(true)
expect(isRunningWithBun(false)).to_equal(false)
```

</details>

#### detects bundled mode from embedded files

- detects bundled mode from embedded files
- Check bundled mode
   - Expected: isInBundledMode(true, 1) is true
   - Expected: isInBundledMode(true, 0) is false
   - Expected: isInBundledMode(false, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects bundled mode from embedded files")
step("Check bundled mode")
expect(isInBundledMode(true, 1)).to_equal(true)
expect(isInBundledMode(true, 0)).to_equal(false)
expect(isInBundledMode(false, 3)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `e85c950a6e7435bfc191efb3c89896a26fa434bbe2f6d8acba15004293a0f996`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e85c950a6e7435bfc191efb3c89896a26fa434bbe2f6d8acba15004293a0f996`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e85c950a6e7435bfc191efb3c89896a26fa434bbe2f6d8acba15004293a0f996`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/bundled_mode_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bundled_mode_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bundled_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bundled_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bundled_mode_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects Bun from version availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bundled_mode_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects bundled mode from embedded files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
