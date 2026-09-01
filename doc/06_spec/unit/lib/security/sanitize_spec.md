# Sanitize Specification

> Tests covering sanitize_html, sanitize_url, sanitize_identifier, is_path_traversal, sanitize_path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sanitize Specification

## Scenarios

### sanitize_html

#### escapes less-than sign

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes less-than sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes less-than sign")
val result = sanitize_html("<script>")
expect(result).to_contain("&lt;")
```

</details>

#### escapes greater-than sign

- escapes greater-than sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes greater-than sign")
val result = sanitize_html("<b>bold</b>")
expect(result).to_contain("&gt;")
```

</details>

#### escapes ampersand

- escapes ampersand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes ampersand")
val result = sanitize_html("a&b")
expect(result).to_contain("&amp;")
```

</details>

#### escapes double quotes

- escapes double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes double quotes")
val result = sanitize_html("say \"hello\"")
expect(result).to_contain("&quot;")
```

</details>

#### escapes single quotes

- escapes single quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes single quotes")
val result = sanitize_html("it's")
expect(result).to_contain("&#x27;")
```

</details>

#### leaves plain text unchanged

- leaves plain text unchanged
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves plain text unchanged")
val result = sanitize_html("hello world")
expect(result).to_equal("hello world")
```

</details>

### sanitize_url

#### rejects javascript scheme

- rejects javascript scheme
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects javascript scheme")
val result = sanitize_url("javascript:alert(1)")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects data scheme

- rejects data scheme
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects data scheme")
val result = sanitize_url("data:text/html,<script>")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts http URLs

- accepts http URLs
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `http://example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts http URLs")
val result = sanitize_url("http://example.com")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("http://example.com")
```

</details>

#### accepts https URLs

- accepts https URLs
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `https://example.com/path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts https URLs")
val result = sanitize_url("https://example.com/path")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("https://example.com/path")
```

</details>

### sanitize_identifier

#### rejects special characters

- rejects special characters
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects special characters")
val result = sanitize_identifier("user;drop")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects starting with digit

- rejects starting with digit
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects starting with digit")
val result = sanitize_identifier("1abc")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts valid identifier

- accepts valid identifier
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `user_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts valid identifier")
val result = sanitize_identifier("user_name")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("user_name")
```

</details>

#### accepts identifier with letters and digits

- accepts identifier with letters and digits
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `item42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identifier with letters and digits")
val result = sanitize_identifier("item42")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("item42")
```

</details>

### is_path_traversal

#### detects ../ traversal

- detects ../ traversal
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects ../ traversal")
val result = is_path_traversal("../etc/passwd")
expect(result).to_equal(true)
```

</details>

#### detects traversal in middle of path

- detects traversal in middle of path
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects traversal in middle of path")
val result = is_path_traversal("/var/www/../etc/shadow")
expect(result).to_equal(true)
```

</details>

#### does not flag normal paths

- does not flag normal paths
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag normal paths")
val result = is_path_traversal("/var/www/html/index.html")
expect(result).to_equal(false)
```

</details>

### sanitize_path

#### rejects traversal paths

- rejects traversal paths
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects traversal paths")
val result = sanitize_path("../../etc/passwd")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts safe paths

- accepts safe paths
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `/static/style.css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts safe paths")
val result = sanitize_path("/static/style.css")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("/static/style.css")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/security/sanitize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sanitize_html, sanitize_url, sanitize_identifier, is_path_traversal, sanitize_path.
- sanitize_html
- sanitize_url
- sanitize_identifier
- is_path_traversal
- sanitize_path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1a00b3c97cc5ce9b839be55b311e5a2597e43fde0cbedf1298ad07753913e1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1a00b3c97cc5ce9b839be55b311e5a2597e43fde0cbedf1298ad07753913e1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1a00b3c97cc5ce9b839be55b311e5a2597e43fde0cbedf1298ad07753913e1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/security/sanitize_spec.spl
mirror: doc/06_spec/unit/lib/security/sanitize_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/security/sanitize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/security/sanitize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/security/sanitize_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes less-than sign' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/sanitize_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes greater-than sign' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/sanitize_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes ampersand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
