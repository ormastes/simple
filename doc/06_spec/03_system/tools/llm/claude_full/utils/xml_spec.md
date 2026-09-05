# Claude Full XML Utils

> Pure Simple coverage for XML and attribute escaping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full XML Utils

Pure Simple coverage for XML and attribute escaping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/xml_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for XML and attribute escaping.

## Scenarios

### Claude full XML utils

#### escapes text content characters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes text content characters
- Check XML text escaping
   - Expected: escapeXml("plain") equals `plain`
   - Expected: escapeXml("a&b<c>d") equals `a&amp;b&lt;c&gt;d`
   - Expected: escapeXml("x'y\"") equals `x'y"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes text content characters")
step("Check XML text escaping")
expect(escapeXml("plain")).to_equal("plain")
expect(escapeXml("a&b<c>d")).to_equal("a&amp;b&lt;c&gt;d")
expect(escapeXml("x'y\"")).to_equal("x'y\"")
```

</details>

#### escapes attribute quote characters too

- escapes attribute quote characters too
- Check quoted attribute escaping
   - Expected: escapeXmlAttr("\"quoted\" and 'single'") equals `&quot;quoted&quot; and &apos;single&apos;`
   - Expected: escapeXmlAttr("<tag attr=\"x&y\">") equals `&lt;tag attr=&quot;x&amp;y&quot;&gt;`
   - Expected: escapeXmlAttr("\"&") equals `&quot;&amp;`
   - Expected: escapeXmlAttr("<>&") equals `&lt;&gt;&amp;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes attribute quote characters too")
step("Check quoted attribute escaping")
expect(escapeXmlAttr("\"quoted\" and 'single'")).to_equal("&quot;quoted&quot; and &apos;single&apos;")
expect(escapeXmlAttr("<tag attr=\"x&y\">")).to_equal("&lt;tag attr=&quot;x&amp;y&quot;&gt;")
expect(escapeXmlAttr("\"&")).to_equal("&quot;&amp;")
expect(escapeXmlAttr("<>&")).to_equal("&lt;&gt;&amp;")
```

</details>

#### escapes ampersands before generated entities

- escapes ampersands before generated entities
- Check escaping order
   - Expected: escapeXml("&lt;") equals `&amp;lt;`
   - Expected: escapeXmlAttr("'&quot;'") equals `&apos;&amp;quot;&apos;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes ampersands before generated entities")
step("Check escaping order")
expect(escapeXml("&lt;")).to_equal("&amp;lt;")
expect(escapeXmlAttr("'&quot;'")).to_equal("&apos;&amp;quot;&apos;")
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

- Canonical SPipe generation for source `1d6698e828ea8566aef11d9c186c46927bb322e935bef4fe6dd0c4fde6d23572`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d6698e828ea8566aef11d9c186c46927bb322e935bef4fe6dd0c4fde6d23572`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d6698e828ea8566aef11d9c186c46927bb322e935bef4fe6dd0c4fde6d23572`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/xml_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/xml_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/xml_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/xml_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/xml_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes text content characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/xml_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes attribute quote characters too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/xml_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes ampersands before generated entities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
