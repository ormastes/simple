# Validate Mcp Native Smoke Source Specification

> Tests covering MCP native smoke validator source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validate Mcp Native Smoke Source Specification

## Scenarios

### MCP native smoke validator source

#### validates Content-Length against raw file bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates Content-Length against raw file bytes
   - Expected: source does not contain `text_to_bytes(raw)`
   - Expected: source does not contain `bytes[pos:pos + prefix.len()]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("validates Content-Length against raw file bytes")
val source = validator_source()

expect(source).to_contain("file_read, file_read_bytes")
expect(source).to_contain("fn validate_content_length_frames(bytes: [u8]) -> bool:")
expect(source).to_contain("val framing_bytes = file_read_bytes(path)")
expect(source).to_contain("validate_content_length_frames(framing_bytes)")
expect(source).to_contain("val crlf_separator: [u8] = [13u8, 10u8, 13u8, 10u8]")
expect(source.contains("text_to_bytes(raw)")).to_equal(false)
expect(source.contains("bytes[pos:pos + prefix.len()]")).to_equal(false)
```

</details>

#### keeps the MCP/LSP NFR evidence gate portable to stock macOS

- keeps the MCP/LSP NFR evidence gate portable to stock macOS
   - Expected: source does not contain `command -v timeout`
   - Expected: source does not contain `gnu_time_required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("keeps the MCP/LSP NFR evidence gate portable to stock macOS")
val source = nfr_gate_source()

expect(source).to_contain("TIME_STYLE=gnu")
expect(source).to_contain("TIME_STYLE=bsd")
expect(source).to_contain("/usr/bin/time -l")
expect(source).to_contain("maximum resident set size")
expect(source).to_contain("perl -e 'alarm shift; exec @ARGV'")
expect(source.contains("command -v timeout")).to_equal(false)
expect(source.contains("gnu_time_required")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP native smoke validator source.
- MCP native smoke validator source

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-SCRIPTS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3b986ac01cb0181e9cea59ba64b72122db9cc1b41b91a9a399ad7cd8563b4e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3b986ac01cb0181e9cea59ba64b72122db9cc1b41b91a9a399ad7cd8563b4e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3b986ac01cb0181e9cea59ba64b72122db9cc1b41b91a9a399ad7cd8563b4e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl
mirror: doc/06_spec/01_unit/scripts/validate_mcp_native_smoke_source_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/scripts/validate_mcp_native_smoke_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/validate_mcp_native_smoke_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates Content-Length against raw file bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the MCP/LSP NFR evidence gate portable to stock macOS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
