# Terminal Credential Facade Specification

> <details>

<!-- sdn-diagram:id=terminal_credential_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_credential_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_credential_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_credential_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Credential Facade Specification

## Scenarios

### nogc_async_mut terminal credential facade

#### re-exports pure credential resolution helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(credential_resolve("plain-secret")).to_equal("plain-secret")
expect(credential_is_encrypted("plain-secret")).to_equal(false)
expect(credential_is_encrypted("encrypted:abc123")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/terminal/credential/terminal_credential_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut terminal credential facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
