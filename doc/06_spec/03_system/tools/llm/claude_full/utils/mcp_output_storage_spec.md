# Claude full MCP output storage pure helpers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude full MCP output storage pure helpers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Claude full MCP output storage helpers

#### describes MCP result formats

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- describes MCP result formats
   - Expected: getFormatDescription("toolResult", nil) equals `Plain text`
   - Expected: getFormatDescription("structuredContent", nil) equals `JSON`
   - Expected: getFormatDescription("structuredContent", Some("")) equals `JSON`
   - Expected: getFormatDescription("structuredContent", Some("{type:object}")) equals `JSON with schema: {type:object}`
   - Expected: getFormatDescription("contentArray", Some("")) equals `JSON array`
   - Expected: getFormatDescription("contentArray", Some("items")) equals `JSON array with schema: items`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("describes MCP result formats")
expect(getFormatDescription("toolResult", nil)).to_equal("Plain text")
expect(getFormatDescription("structuredContent", nil)).to_equal("JSON")
expect(getFormatDescription("structuredContent", Some(""))).to_equal("JSON")
expect(getFormatDescription("structuredContent", Some("{type:object}"))).to_equal("JSON with schema: {type:object}")
expect(getFormatDescription("contentArray", Some(""))).to_equal("JSON array")
expect(getFormatDescription("contentArray", Some("items"))).to_equal("JSON array with schema: items")
```

</details>

#### builds large output read instructions

- builds large output read instructions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds large output read instructions")
val text = getLargeOutputInstructions("/tmp/out.txt", 1234567, "Plain text", Some(4096))
expect(text).to_contain("1,234,567 characters")
expect(text).to_contain("Bash output is limited to 4,096 chars.")
expect(text).to_contain("***If you did not read the entire content, you MUST explicitly state this.***")
```

</details>

#### treats zero max read length like no limit

- treats zero max read length like no limit
   - Expected: text equals `getLargeOutputInstructions("/tmp/out.txt", 12, "JSON", nil)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats zero max read length like no limit")
val text = getLargeOutputInstructions("/tmp/out.txt", 12, "JSON", Some(0))
expect(text).to_contain("If you receive truncation warnings when reading the file, reduce the chunk size")
expect(text).to_equal(getLargeOutputInstructions("/tmp/out.txt", 12, "JSON", nil))
```

</details>

#### maps known mime types to read-friendly extensions

- maps known mime types to read-friendly extensions
   - Expected: extensionForMimeType(Some("application/pdf; charset=binary")) equals `pdf`
   - Expected: extensionForMimeType(Some("IMAGE/JPEG")) equals `jpg`
   - Expected: extensionForMimeType(Some("application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")) equals `xlsx`
   - Expected: extensionForMimeType(nil) equals `bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps known mime types to read-friendly extensions")
expect(extensionForMimeType(Some("application/pdf; charset=binary"))).to_equal("pdf")
expect(extensionForMimeType(Some("IMAGE/JPEG"))).to_equal("jpg")
expect(extensionForMimeType(Some("application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"))).to_equal("xlsx")
expect(extensionForMimeType(nil)).to_equal("bin")
```

</details>

#### classifies text-ish content as non-binary

- classifies text-ish content as non-binary
   - Expected: isBinaryContentType("text/plain") is false
   - Expected: isBinaryContentType("application/activity+json") is false
   - Expected: isBinaryContentType("application/xml") is false
   - Expected: isBinaryContentType("application/javascript") is false
   - Expected: isBinaryContentType("application/pdf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies text-ish content as non-binary")
expect(isBinaryContentType("text/plain")).to_equal(false)
expect(isBinaryContentType("application/activity+json")).to_equal(false)
expect(isBinaryContentType("application/xml")).to_equal(false)
expect(isBinaryContentType("application/javascript")).to_equal(false)
expect(isBinaryContentType("application/pdf")).to_equal(true)
```

</details>

#### builds saved binary blob messages

- builds saved binary blob messages
   - Expected: message equals `Tool result: Binary content (application/pdf, 2KB) saved to /tmp/blob.pdf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds saved binary blob messages")
val message = getBinaryBlobSavedMessage("/tmp/blob.pdf", Some("application/pdf"), 2048, "Tool result: ")
expect(message).to_equal("Tool result: Binary content (application/pdf, 2KB) saved to /tmp/blob.pdf")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e2e0f1d7d98099fb99d45ea148bfc75ac582ce82819d523dabdaf87af2df1899`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2e0f1d7d98099fb99d45ea148bfc75ac582ce82819d523dabdaf87af2df1899`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2e0f1d7d98099fb99d45ea148bfc75ac582ce82819d523dabdaf87af2df1899`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes MCP result formats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds large output read instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/mcp_output_storage_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats zero max read length like no limit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
