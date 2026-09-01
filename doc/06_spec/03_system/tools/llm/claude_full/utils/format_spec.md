# Claude Full format utils

> Pure Simple coverage for integer-safe display formatters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full format utils

Pure Simple coverage for integer-safe display formatters.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for integer-safe display formatters.

## Scenarios

### Claude full format utils

#### formats file sizes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats file sizes
- Check byte and unit formatting
   - Expected: formatFileSize(500) equals `500 bytes`
   - Expected: formatFileSize(1536) equals `1.5KB`
   - Expected: formatFileSize(1048576) equals `1MB`
   - Expected: formatFileSize(1610612736) equals `1.5GB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats file sizes")
step("Check byte and unit formatting")
expect(formatFileSize(500)).to_equal("500 bytes")
expect(formatFileSize(1536)).to_equal("1.5KB")
expect(formatFileSize(1048576)).to_equal("1MB")
expect(formatFileSize(1610612736)).to_equal("1.5GB")
```

</details>

#### formats short seconds with one decimal place when needed

- formats short seconds with one decimal place when needed
- Check short seconds
   - Expected: formatSecondsShort(1234) equals `1.2s`
   - Expected: formatSecondsShort(1000) equals `1s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats short seconds with one decimal place when needed")
step("Check short seconds")
expect(formatSecondsShort(1234)).to_equal("1.2s")
expect(formatSecondsShort(1000)).to_equal("1s")
```

</details>

#### formats sub-minute durations

- formats sub-minute durations
- Check seconds
   - Expected: formatDuration(0) equals `0s`
   - Expected: formatDuration(500) equals `0.5s`
   - Expected: formatDuration(1234) equals `1s`
   - Expected: formatDuration(59999) equals `59s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats sub-minute durations")
step("Check seconds")
expect(formatDuration(0)).to_equal("0s")
expect(formatDuration(500)).to_equal("0.5s")
expect(formatDuration(1234)).to_equal("1s")
expect(formatDuration(59999)).to_equal("59s")
```

</details>

#### formats longer durations and rounding carry

- formats longer durations and rounding carry
- Check composite durations
   - Expected: formatDuration(65000) equals `1m 5s`
   - Expected: formatDuration(3661000) equals `1h 1m 1s`
   - Expected: formatDuration(3599500) equals `1h 0m 0s`
   - Expected: formatDuration(90061000) equals `1d 1h 1m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats longer durations and rounding carry")
step("Check composite durations")
expect(formatDuration(65000)).to_equal("1m 5s")
expect(formatDuration(3661000)).to_equal("1h 1m 1s")
expect(formatDuration(3599500)).to_equal("1h 0m 0s")
expect(formatDuration(90061000)).to_equal("1d 1h 1m")
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

- Canonical SPipe generation for source `5d3b11775bfc801f88ad4bfd338e19485d9590718495b585bbaa854c3ffe5f12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d3b11775bfc801f88ad4bfd338e19485d9590718495b585bbaa854c3ffe5f12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d3b11775bfc801f88ad4bfd338e19485d9590718495b585bbaa854c3ffe5f12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/format_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/format_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats file sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/format_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats short seconds with one decimal place when needed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/format_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats sub-minute durations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
