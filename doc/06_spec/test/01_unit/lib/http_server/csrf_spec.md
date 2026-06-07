# csrf_spec

> Tests for CSRF token generation, validation, and method exemptions. Validates that tokens are generated, matched, and that safe methods are exempt.

<!-- sdn-diagram:id=csrf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=csrf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

csrf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=csrf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# csrf_spec

Tests for CSRF token generation, validation, and method exemptions. Validates that tokens are generated, matched, and that safe methods are exempt.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-011 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/csrf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for CSRF token generation, validation, and method exemptions.
Validates that tokens are generated, matched, and that safe methods are exempt.

## Scenarios

### CSRF token generation

#### generates a non-empty token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = generate_csrf_token()
val is_non_empty = token.len() > 0
expect(is_non_empty).to_equal(true)
```

</details>

#### generates tokens of sufficient length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = generate_csrf_token()
val is_long_enough = token.len() >= 32
expect(is_long_enough).to_equal(true)
```

</details>

### CSRF token validation

#### validates matching tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "abc123def456ghi789jkl012mno345pq"
val result = validate_csrf_token(token, token)
expect(result).to_equal(true)
```

</details>

#### rejects mismatched tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token_a = "abc123def456ghi789jkl012mno345pq"
val token_b = "zzz999yyy888xxx777www666vvv555uu"
val result = validate_csrf_token(token_a, token_b)
expect(result).to_equal(false)
```

</details>

#### rejects empty token against valid token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "abc123def456ghi789jkl012mno345pq"
val result = validate_csrf_token("", token)
expect(result).to_equal(false)
```

</details>

### CSRF method exemptions

#### exempts GET by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_csrf_exempt_method("GET")
expect(result).to_equal(true)
```

</details>

#### exempts HEAD by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_csrf_exempt_method("HEAD")
expect(result).to_equal(true)
```

</details>

#### exempts OPTIONS by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_csrf_exempt_method("OPTIONS")
expect(result).to_equal(true)
```

</details>

#### does not exempt POST

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_csrf_exempt_method("POST")
expect(result).to_equal(false)
```

</details>

#### does not exempt DELETE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_csrf_exempt_method("DELETE")
expect(result).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
