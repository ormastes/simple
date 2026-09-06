# capability_policy_spec

> Tests for capability-based security policy enforcement. Validates default-deny, explicit grant/deny, allow-all, and capability name parsing.

<!-- sdn-diagram:id=capability_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# capability_policy_spec

Tests for capability-based security policy enforcement. Validates default-deny, explicit grant/deny, allow-all, and capability name parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-020 |
| Category | UI Security |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/ui/capability_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for capability-based security policy enforcement.
Validates default-deny, explicit grant/deny, allow-all, and capability name parsing.

## Scenarios

### Default-deny policy

#### blocks ungranted capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = default_deny_policy()
val result = check_capability(policy, "file_read")
expect(result).to_equal(false)
```

</details>

#### blocks all capabilities when nothing is granted

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = default_deny_policy()
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
val net = check_capability(policy, "network")
expect(read).to_equal(false)
expect(write).to_equal(false)
expect(net).to_equal(false)
```

</details>

### Explicit capability grant

#### passes after explicit grant

1. var policy = default deny policy
2. policy = grant capability
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = default_deny_policy()
policy = grant_capability(policy, "file_read")
val result = check_capability(policy, "file_read")
expect(result).to_equal(true)
```

</details>

#### only grants the specified capability

1. var policy = default deny policy
2. policy = grant capability
   - Expected: read is true
   - Expected: write is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = default_deny_policy()
policy = grant_capability(policy, "file_read")
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
expect(read).to_equal(true)
expect(write).to_equal(false)
```

</details>

### Explicit deny overrides grant

#### deny overrides a previous grant

1. var policy = default deny policy
2. policy = grant capability
3. policy = deny capability
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = default_deny_policy()
policy = grant_capability(policy, "network")
policy = deny_capability(policy, "network")
val result = check_capability(policy, "network")
expect(result).to_equal(false)
```

</details>

### Allow-all policy

#### passes everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = allow_all_policy()
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
val net = check_capability(policy, "network")
expect(read).to_equal(true)
expect(write).to_equal(true)
expect(net).to_equal(true)
```

</details>

### parse_capability round-trips

#### round-trips file_read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = parse_capability("file_read")
val name = capability_to_string(cap)
expect(name).to_equal("file_read")
```

</details>

#### round-trips file_write

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = parse_capability("file_write")
val name = capability_to_string(cap)
expect(name).to_equal("file_write")
```

</details>

#### round-trips network

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = parse_capability("network")
val name = capability_to_string(cap)
expect(name).to_equal("network")
```

</details>

#### round-trips process_spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = parse_capability("process_spawn")
val name = capability_to_string(cap)
expect(name).to_equal("process_spawn")
```

</details>

#### round-trips env_access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = parse_capability("env_access")
val name = capability_to_string(cap)
expect(name).to_equal("env_access")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
