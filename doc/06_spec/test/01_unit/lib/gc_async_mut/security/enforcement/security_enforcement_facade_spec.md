# Security Enforcement Facade Specification

> <details>

<!-- sdn-diagram:id=security_enforcement_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_enforcement_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_enforcement_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_enforcement_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security Enforcement Facade Specification

## Scenarios

### gc_async_mut security enforcement facade

#### re-exports capability parsing and resolver grant helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_users = Capability.Read(resource: "users")
val read_any = Capability.Read(resource: "*")
val write_users = Capability.Write(resource: "users")
expect(read_any.matches(read_users)).to_equal(true)
expect(read_users.matches(write_users)).to_equal(false)
expect(parse_capability("admin:*").to_string()).to_equal("admin:*")

val store = CapabilityStore.new()
val resolver = PermissionResolver.new(store)
val denied = resolver.resolve("alice", read_users, [])
expect(is_granted(denied)).to_equal(false)
expect(is_granted(PermissionResult.GrantedByRole(role: "admin"))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/security/enforcement/security_enforcement_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut security enforcement facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
