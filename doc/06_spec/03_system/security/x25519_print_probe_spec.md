# X25519 Print Probe Specification

> <details>

<!-- sdn-diagram:id=x25519_print_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x25519_print_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x25519_print_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x25519_print_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519 Print Probe Specification

## Scenarios

### x25519 print probe portable smoke

#### records RFC 7748 base vector metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a".len()).to_equal(64)
expect("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a".len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/x25519_print_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x25519 print probe portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
