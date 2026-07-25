# Cross Module Result Match Repro Specification

> <details>

<!-- sdn-diagram:id=cross_module_result_match_repro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cross_module_result_match_repro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cross_module_result_match_repro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cross_module_result_match_repro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Module Result Match Repro Specification

## Scenarios

### cross-module text.from_char_code regression

#### REQ-INTERP-CMR-001: base64url_decode round-trip across module boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# base64url_decode internally used the broken `text.from_char_code(n)` idiom.
# Encode "hello" then decode; the decode path crashed pre-fix with
# `variable 'text' not found`.
val original = "hello"
val encoded = base64url_encode(original)
val decoded = base64url_decode(encoded)
expect(decoded).to_equal(original)
```

</details>

#### REQ-INTERP-CMR-002: base64url_decode on JWT-style input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "aGVsbG8" is base64url for "hello" (no padding).
val s = base64url_decode("aGVsbG8")
expect(s).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cross_module_result_match_repro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cross-module text.from_char_code regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
