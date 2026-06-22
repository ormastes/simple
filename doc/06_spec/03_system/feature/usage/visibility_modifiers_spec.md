# Access Control with Visibility Modifiers

> Visibility modifiers (`public`, `private`, `protected`) control which scopes may access a given struct field, class method, or module-level declaration. `public` members are accessible everywhere, `private` members only within the defining class or module, and `protected` members within the class and its submodules. This spec is a placeholder that will be expanded once the visibility modifier feature is implemented; planned tests will verify compile-time rejection of illegal access, correct scoping across module boundaries, and interaction with the existing MDSOC capsule visibility system.

<!-- sdn-diagram:id=visibility_modifiers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=visibility_modifiers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

visibility_modifiers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=visibility_modifiers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Control with Visibility Modifiers

Visibility modifiers (`public`, `private`, `protected`) control which scopes may access a given struct field, class method, or module-level declaration. `public` members are accessible everywhere, `private` members only within the defining class or module, and `protected` members within the class and its submodules. This spec is a placeholder that will be expanded once the visibility modifier feature is implemented; planned tests will verify compile-time rejection of illegal access, correct scoping across module boundaries, and interaction with the existing MDSOC capsule visibility system.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-038 |
| Category | Language |
| Status | Planned |
| Source | `test/03_system/feature/usage/visibility_modifiers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Visibility modifiers (`public`, `private`, `protected`) control which scopes may
access a given struct field, class method, or module-level declaration. `public`
members are accessible everywhere, `private` members only within the defining
class or module, and `protected` members within the class and its submodules.
This spec is a placeholder that will be expanded once the visibility modifier
feature is implemented; planned tests will verify compile-time rejection of
illegal access, correct scoping across module boundaries, and interaction with
the existing MDSOC capsule visibility system.

## Syntax

```simple
# Planned visibility modifier syntax (not yet implemented)
class Account:
private balance: i64
public fn deposit(amount: i64):
self.balance = self.balance + amount
protected fn audit_log(msg: Str):
print(msg)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `public` | Member is accessible from any scope |
| `private` | Member is accessible only within its declaring class or module |
| `protected` | Member is accessible within its class and submodules |
| Compile-time enforcement | Illegal access should be rejected during compilation, not at runtime |

## Scenarios

### Visibility Modifiers

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement visibility modifier tests when feature is available
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
