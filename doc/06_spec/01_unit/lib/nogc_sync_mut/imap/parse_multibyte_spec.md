# Parse Multibyte Specification

> Tests covering imap_split_at_first_space -- multibyte UTF-8 safety, imap_strip_crlf -- multibyte UTF-8 safety, imap_parse_capability_tokens -- multibyte UTF-8 safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Multibyte Specification

## Scenarios

### imap_split_at_first_space -- multibyte UTF-8 safety

#### splits correctly when a multibyte char precedes the space (reproduces the bug)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits correctly when a multibyte char precedes the space (reproduces the bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits correctly when a multibyte char precedes the space (reproduces the bug)")
val parts = imap_split_at_first_space("caf\u{e9} bar")
assert_equal(parts[0], "caf\u{e9}")
assert_equal(parts[1], "bar")
```

</details>

#### handles multibyte at the first position

- handles multibyte at the first position


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at the first position")
val parts = imap_split_at_first_space("\u{e9}bc def")
assert_equal(parts[0], "\u{e9}bc")
assert_equal(parts[1], "def")
```

</details>

#### handles multibyte adjacent to the space (last byte before it)

- handles multibyte adjacent to the space (last byte before it)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte adjacent to the space (last byte before it)")
val parts = imap_split_at_first_space("x\u{e9} y")
assert_equal(parts[0], "x\u{e9}")
assert_equal(parts[1], "y")
```

</details>

#### handles a pure-multibyte string with no space

- handles a pure-multibyte string with no space


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles a pure-multibyte string with no space")
val parts = imap_split_at_first_space("\u{e9}\u{e8}\u{ea}")
assert_equal(parts[0], "\u{e9}\u{e8}\u{ea}")
```

</details>

#### handles mixed ASCII + multibyte across two words

- handles mixed ASCII + multibyte across two words


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles mixed ASCII + multibyte across two words")
val parts = imap_split_at_first_space("a1 caf\u{e9} tag")
assert_equal(parts[0], "a1")
assert_equal(parts[1], "caf\u{e9} tag")
```

</details>

### imap_strip_crlf -- multibyte UTF-8 safety

#### leaves a multibyte-terminated line without CRLF unchanged

- leaves a multibyte-terminated line without CRLF unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a multibyte-terminated line without CRLF unchanged")
assert_equal(imap_strip_crlf("caf\u{e9}"), "caf\u{e9}")
```

</details>

#### strips CRLF following multibyte content

- strips CRLF following multibyte content


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips CRLF following multibyte content")
assert_equal(imap_strip_crlf("caf\u{e9}\r\n"), "caf\u{e9}")
```

</details>

#### strips bare LF following multibyte content

- strips bare LF following multibyte content


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips bare LF following multibyte content")
assert_equal(imap_strip_crlf("caf\u{e9}\n"), "caf\u{e9}")
```

</details>

### imap_parse_capability_tokens -- multibyte UTF-8 safety

#### tokenizes capability data containing a multibyte token

- tokenizes capability data containing a multibyte token


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tokenizes capability data containing a multibyte token")
val toks = imap_parse_capability_tokens("IMAP4rev1 X-CAF\u{e9} STARTTLS")
assert_equal(toks[0], "IMAP4rev1")
assert_equal(toks[1], "X-CAF\u{e9}")
assert_equal(toks[2], "STARTTLS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering imap_split_at_first_space -- multibyte UTF-8 safety, imap_strip_crlf -- multibyte UTF-8 safety, imap_parse_capability_tokens -- multibyte UTF-8 safety.
- imap_split_at_first_space -- multibyte UTF-8 safety
- imap_strip_crlf -- multibyte UTF-8 safety
- imap_parse_capability_tokens -- multibyte UTF-8 safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BUG-MIXED-INDEX-IMAP-PARSE`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4eec7db3a6bac8c89b6eaed6519bae9632a8a6e60ec448cffd846935281be68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4eec7db3a6bac8c89b6eaed6519bae9632a8a6e60ec448cffd846935281be68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4eec7db3a6bac8c89b6eaed6519bae9632a8a6e60ec448cffd846935281be68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits correctly when a multibyte char precedes the space (reproduces the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte at the first position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte adjacent to the space (last byte before it)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
