# sanitize_spec

> Tests for input sanitization functions. Validates HTML escaping, URL scheme checks, identifier rules, and path traversal detection.

<!-- sdn-diagram:id=sanitize_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sanitize_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sanitize_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sanitize_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sanitize_spec

Tests for input sanitization functions. Validates HTML escaping, URL scheme checks, identifier rules, and path traversal detection.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-030 |
| Category | Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/security/sanitize_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for input sanitization functions.
Validates HTML escaping, URL scheme checks, identifier rules, and path traversal detection.

## Scenarios

### sanitize_html

#### escapes less-than sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("<script>")
expect(result).to_contain("&lt;")
```

</details>

#### escapes greater-than sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("<b>bold</b>")
expect(result).to_contain("&gt;")
```

</details>

#### escapes ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("a&b")
expect(result).to_contain("&amp;")
```

</details>

#### escapes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("say \"hello\"")
expect(result).to_contain("&quot;")
```

</details>

#### escapes single quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("it's")
expect(result).to_contain("&#x27;")
```

</details>

#### leaves plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("hello world")
expect(result).to_equal("hello world")
```

</details>

### sanitize_url

#### rejects javascript scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("javascript:alert(1)")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects data scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("data:text/html,<script>")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts http URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("http://example.com")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("http://example.com")
```

</details>

#### accepts https URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("https://example.com/path")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("https://example.com/path")
```

</details>

### sanitize_identifier

#### rejects special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("user;drop")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects starting with digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("1abc")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts valid identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("user_name")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("user_name")
```

</details>

#### accepts identifier with letters and digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("item42")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("item42")
```

</details>

### is_path_traversal

#### detects ../ traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_path_traversal("../etc/passwd")
expect(result).to_equal(true)
```

</details>

#### detects traversal in middle of path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_path_traversal("/var/www/../etc/shadow")
expect(result).to_equal(true)
```

</details>

#### does not flag normal paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_path_traversal("/var/www/html/index.html")
expect(result).to_equal(false)
```

</details>

### sanitize_path

#### rejects traversal paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_path("../../etc/passwd")
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts safe paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_path("/static/style.css")
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal("/static/style.css")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
