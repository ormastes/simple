# Claude Full Hyperlink

> Pure Simple coverage for OSC 8 hyperlink output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hyperlink

Pure Simple coverage for OSC 8 hyperlink output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/hyperlink_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for OSC 8 hyperlink output.

## Scenarios

### Claude full hyperlink parity

#### falls back to the url without hyperlink support

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- falls back to the url without hyperlink support
- Check unsupported terminal route
   - Expected: createHyperlink("https://example.com", Some("Example"), false) equals `https://example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back to the url without hyperlink support")
step("Check unsupported terminal route")
expect(createHyperlink("https://example.com", Some("Example"), false)).to_equal("https://example.com")
```

</details>

#### uses url as content when content is missing

- uses url as content when content is missing
- Check missing display text
   - Expected: createHyperlink("https://example.com", nil, true) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses url as content when content is missing")
step("Check missing display text")
val expected = "\u001B]8;;https://example.com\u0007\u001B[34mhttps://example.com\u001B[39m\u001B]8;;\u0007"
expect(createHyperlink("https://example.com", nil, true)).to_equal(expected)
```

</details>

#### wraps custom content with OSC 8 and blue foreground

- wraps custom content with OSC 8 and blue foreground
- Check custom display text
   - Expected: createHyperlink("https://example.com", Some("Example"), true) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps custom content with OSC 8 and blue foreground")
step("Check custom display text")
val expected = "\u001B]8;;https://example.com\u0007\u001B[34mExample\u001B[39m\u001B]8;;\u0007"
expect(createHyperlink("https://example.com", Some("Example"), true)).to_equal(expected)
```

</details>

#### preserves explicit empty content

- preserves explicit empty content
- Check empty display text
   - Expected: createHyperlink("https://example.com", Some(""), true) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves explicit empty content")
step("Check empty display text")
val expected = "\u001B]8;;https://example.com\u0007\u001B]8;;\u0007"
expect(createHyperlink("https://example.com", Some(""), true)).to_equal(expected)
```

</details>

#### reopens blue after inner foreground closes

- reopens blue after inner foreground closes
- Check chalk blue nesting behavior
   - Expected: createHyperlink("https://example.com", Some(content), true) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reopens blue after inner foreground closes")
step("Check chalk blue nesting behavior")
val content = "\u001B[31mR\u001B[39mZ"
val expected = "\u001B]8;;https://example.com\u0007\u001B[34m\u001B[31mR\u001B[34mZ\u001B[39m\u001B]8;;\u0007"
expect(createHyperlink("https://example.com", Some(content), true)).to_equal(expected)
```

</details>

#### closes and reopens blue across newlines

- closes and reopens blue across newlines
- Check chalk newline behavior
   - Expected: createHyperlink("https://example.com", Some("A\nB"), true) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closes and reopens blue across newlines")
step("Check chalk newline behavior")
val expected = "\u001B]8;;https://example.com\u0007\u001B[34mA\u001B[39m\n\u001B[34mB\u001B[39m\u001B]8;;\u0007"
expect(createHyperlink("https://example.com", Some("A\nB"), true)).to_equal(expected)
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

- Canonical SPipe generation for source `aad7dcf3df8864bfdf8d47f75a28d44b0d3c2da8f7d4b6b24a3f1b43fef79c0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aad7dcf3df8864bfdf8d47f75a28d44b0d3c2da8f7d4b6b24a3f1b43fef79c0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aad7dcf3df8864bfdf8d47f75a28d44b0d3c2da8f7d4b6b24a3f1b43fef79c0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/hyperlink_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/hyperlink_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/hyperlink_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/hyperlink_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/hyperlink_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the url without hyperlink support' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/hyperlink_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses url as content when content is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/hyperlink_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps custom content with OSC 8 and blue foreground' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
