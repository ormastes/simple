# Claude Full embedded tools

> Pure Simple coverage for embedded search tool gating.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full embedded tools

Pure Simple coverage for embedded search tool gating.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/embedded_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for embedded search tool gating.

## Scenarios

### Claude full embedded tools

#### requires the embedded search tools env flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires the embedded search tools env flag
- Check disabled env values
   - Expected: hasEmbeddedSearchTools(nil, nil) is false
   - Expected: hasEmbeddedSearchTools(Some("false"), nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the embedded search tools env flag")
step("Check disabled env values")
expect(hasEmbeddedSearchTools(nil, nil)).to_equal(false)
expect(hasEmbeddedSearchTools(Some("false"), nil)).to_equal(false)
```

</details>

#### allows embedded tools outside excluded SDK entrypoints

- allows embedded tools outside excluded SDK entrypoints
- Check allowed entrypoints
   - Expected: hasEmbeddedSearchTools(Some("1"), nil) is true
   - Expected: hasEmbeddedSearchTools(Some("true"), Some("ant-native")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows embedded tools outside excluded SDK entrypoints")
step("Check allowed entrypoints")
expect(hasEmbeddedSearchTools(Some("1"), nil)).to_equal(true)
expect(hasEmbeddedSearchTools(Some("true"), Some("ant-native"))).to_equal(true)
```

</details>

#### excludes SDK and local agent entrypoints

- excludes SDK and local agent entrypoints
- Check excluded entrypoints
   - Expected: hasEmbeddedSearchTools(Some("1"), Some("sdk-ts")) is false
   - Expected: hasEmbeddedSearchTools(Some("1"), Some("sdk-py")) is false
   - Expected: hasEmbeddedSearchTools(Some("1"), Some("sdk-cli")) is false
   - Expected: hasEmbeddedSearchTools(Some("1"), Some("local-agent")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes SDK and local agent entrypoints")
step("Check excluded entrypoints")
expect(hasEmbeddedSearchTools(Some("1"), Some("sdk-ts"))).to_equal(false)
expect(hasEmbeddedSearchTools(Some("1"), Some("sdk-py"))).to_equal(false)
expect(hasEmbeddedSearchTools(Some("1"), Some("sdk-cli"))).to_equal(false)
expect(hasEmbeddedSearchTools(Some("1"), Some("local-agent"))).to_equal(false)
```

</details>

#### returns the embedding binary path

- returns the embedding binary path
- Check exec path passthrough
   - Expected: embeddedSearchToolsBinaryPath("/opt/claude") equals `/opt/claude`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns the embedding binary path")
step("Check exec path passthrough")
expect(embeddedSearchToolsBinaryPath("/opt/claude")).to_equal("/opt/claude")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70af22b554eb366fb1ef05d20d018e5fd2de1369cbcadef475bcb92bc9284fb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70af22b554eb366fb1ef05d20d018e5fd2de1369cbcadef475bcb92bc9284fb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70af22b554eb366fb1ef05d20d018e5fd2de1369cbcadef475bcb92bc9284fb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/embedded_tools_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/embedded_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/embedded_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/embedded_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/embedded_tools_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the embedded search tools env flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/embedded_tools_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows embedded tools outside excluded SDK entrypoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/embedded_tools_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes SDK and local agent entrypoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
