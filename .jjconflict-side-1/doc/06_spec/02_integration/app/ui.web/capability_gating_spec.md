# Capability Gating Specification

> <details>

<!-- sdn-diagram:id=capability_gating_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_gating_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_gating_spec -> std
capability_gating_spec -> app
capability_gating_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_gating_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Gating Specification

## Scenarios

### OriginGuard.check

#### allows a matching origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://app.example.com"])
val headers = "Origin: https://app.example.com\r\nHost: app.example.com\r\n"
val result = guard.check(headers)
expect(result.is_ok()).to_equal(true)
```

</details>

### SessionToken

#### serializes a token with the grant id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = SessionToken.issue("dev", "https://app.example.com", 60000u64, "test-secret-key")
expect(tok.serialize().contains(".dev.")).to_equal(true)
```

</details>

#### percent-encodes dots in the serialized origin segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = SessionToken.issue("dev", "https://app.example.com", 60000u64, "test-secret-key")
expect(tok.serialize().contains("%2E")).to_equal(true)
```

</details>

#### rejects tokens with extra separators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = SessionToken.parse("token.dev.https%2E%2Eapp.example.com.123.sig.extra")
expect(result.is_err()).to_be(true)
```

</details>

### CapabilityPolicy

#### default-deny policy denies InputInject

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("win-1")
val result = check_capability(policy, Capability.InputInject)
expect(result.is_err()).to_equal(true)
```

</details>

#### granting InputInject allows it

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("win-1")
val granted_policy = grant(policy, Capability.InputInject)
val result = check_capability(granted_policy, Capability.InputInject)
expect(result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ui.web/capability_gating_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OriginGuard.check
- SessionToken
- CapabilityPolicy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
