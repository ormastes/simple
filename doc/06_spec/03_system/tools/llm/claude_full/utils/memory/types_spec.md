# Claude Full memory types

> Pure Simple coverage for memory type values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full memory types

Pure Simple coverage for memory type values.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/memory/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for memory type values.

## Scenarios

### Claude full memory types

#### exposes base memory type values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes base memory type values
- Check base values
   - Expected: memoryTypeValues(false) equals `["User", "Project", "Local", "Managed", "AutoMem"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes base memory type values")
step("Check base values")
expect(memoryTypeValues(false)).to_equal(["User", "Project", "Local", "Managed", "AutoMem"])
```

</details>

#### includes TeamMem when the feature is enabled

- includes TeamMem when the feature is enabled
- Check TeamMem feature value
   - Expected: memoryTypeValues(true) equals `["User", "Project", "Local", "Managed", "AutoMem", "TeamMem"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes TeamMem when the feature is enabled")
step("Check TeamMem feature value")
expect(memoryTypeValues(true)).to_equal(["User", "Project", "Local", "Managed", "AutoMem", "TeamMem"])
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

- Canonical SPipe generation for source `b9cccbc1e1465562d76977e297e8da3e4a795062e0e4d661991fe1055b701b8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9cccbc1e1465562d76977e297e8da3e4a795062e0e4d661991fe1055b701b8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9cccbc1e1465562d76977e297e8da3e4a795062e0e4d661991fe1055b701b8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/memory/types_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/memory/types_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/memory/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/memory/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/memory/types_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes base memory type values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/memory/types_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes TeamMem when the feature is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
