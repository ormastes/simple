# Security Sanitize Utf8 Specification

> Tests covering strip_html_tags UTF-8 index space.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security Sanitize Utf8 Specification

## Scenarios

### strip_html_tags UTF-8 index space

#### keeps a 2-byte character as tag content

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a 2-byte character as tag content
   - Expected: strip_html_tags("<p>\u{e9}</p>") equals `\u{e9}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a 2-byte character as tag content")
expect(strip_html_tags("<p>\u{e9}</p>")).to_equal("\u{e9}")
```

</details>

#### keeps a 3-byte CJK character as tag content

- keeps a 3-byte CJK character as tag content
   - Expected: strip_html_tags("<p>\u{4e2d}</p>") equals `\u{4e2d}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a 3-byte CJK character as tag content")
expect(strip_html_tags("<p>\u{4e2d}</p>")).to_equal("\u{4e2d}")
```

</details>

#### keeps a 4-byte emoji as tag content

- keeps a 4-byte emoji as tag content
   - Expected: strip_html_tags("<p>\u{1f389}</p>") equals `\u{1f389}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a 4-byte emoji as tag content")
expect(strip_html_tags("<p>\u{1f389}</p>")).to_equal("\u{1f389}")
```

</details>

#### ASCII control -- removes tags around single-byte content

- ASCII control -- removes tags around single-byte content
   - Expected: strip_html_tags("<p>e</p>") equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ASCII control -- removes tags around single-byte content")
expect(strip_html_tags("<p>e</p>")).to_equal("e")
```

</details>

#### keeps mixed-width text intact across several tags

- keeps mixed-width text intact across several tags
   - Expected: strip_html_tags("<b>caf\u{e9}</b> <i>\u{4e2d}</i>") equals `caf\u{e9} \u{4e2d}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps mixed-width text intact across several tags")
expect(strip_html_tags("<b>caf\u{e9}</b> <i>\u{4e2d}</i>")).to_equal("caf\u{e9} \u{4e2d}")
```

</details>

#### preserves byte length of multi-byte tag content

- preserves byte length of multi-byte tag content
   - Expected: strip_html_tags("<p>caf\u{e9}</p>").len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves byte length of multi-byte tag content")
expect(strip_html_tags("<p>caf\u{e9}</p>").len()).to_equal(5)
```

</details>

#### keeps the tag state machine in sync after a multi-byte character

- keeps the tag state machine in sync after a multi-byte character
   - Expected: strip_html_tags("\u{e9}<b>x</b>y") equals `\u{e9}xy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tag state machine in sync after a multi-byte character")
expect(strip_html_tags("\u{e9}<b>x</b>y")).to_equal("\u{e9}xy")
```

</details>

#### does not leak tag characters after a multi-byte character

- does not leak tag characters after a multi-byte character
   - Expected: strip_html_tags("<p>\u{e9}</p>") does not contain `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not leak tag characters after a multi-byte character")
expect(strip_html_tags("<p>\u{e9}</p>").contains(">")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security_sanitize_utf8_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strip_html_tags UTF-8 index space.
- strip_html_tags UTF-8 index space

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8bed6029bd713de242101b3af7c3f4283055a8b42abb2f480dec14f59599ffe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8bed6029bd713de242101b3af7c3f4283055a8b42abb2f480dec14f59599ffe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8bed6029bd713de242101b3af7c3f4283055a8b42abb2f480dec14f59599ffe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/security_sanitize_utf8_spec.spl
mirror: doc/06_spec/01_unit/lib/security_sanitize_utf8_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/security_sanitize_utf8_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/security_sanitize_utf8_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/security_sanitize_utf8_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/security_sanitize_utf8_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a 2-byte character as tag content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security_sanitize_utf8_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a 3-byte CJK character as tag content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security_sanitize_utf8_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a 4-byte emoji as tag content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
