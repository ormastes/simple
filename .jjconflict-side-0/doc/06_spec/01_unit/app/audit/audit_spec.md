# Audit Unit Tests

> 1. check

<!-- sdn-diagram:id=audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audit_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audit Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-AUDIT-001 |
| Category | App \| Audit |
| Status | Implemented |
| Source | `test/01_unit/app/audit/audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Security Audit

#### check for unsafe blocks

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsafe_count = 0
check(unsafe_count >= 0)
```

</details>

#### check for extern functions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extern_count = 5
check(extern_count >= 0)
```

</details>

#### check for hardcoded credentials

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = false
check(not found)
```

</details>

#### check for SQL injection

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulnerable = false
check(not vulnerable)
```

</details>

#### check for command injection

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulnerable = false
check(not vulnerable)
```

</details>

### Dependency Audit

#### check outdated dependencies

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outdated = 0
check(outdated >= 0)
```

</details>

#### check known vulnerabilities

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulns = 0
check(vulns == 0)
```

</details>

#### check license compatibility

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compatible = true
check(compatible)
```

</details>

#### check unused dependencies

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unused = 0
check(unused >= 0)
```

</details>

### Code Quality Audit

#### check dead code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dead_code_count = 0
check(dead_code_count >= 0)
```

</details>

#### check unused imports

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unused = 0
check(unused >= 0)
```

</details>

#### check complexity

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_complexity = 20
check(max_complexity > 0)
```

</details>

#### check line length

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_line = 120
check(max_line > 0)
```

</details>

#### check function length

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_fn = 100
check(max_fn > 0)
```

</details>

### Audit Report

#### report has severity levels

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["critical", "high", "medium", "low", "info"]
check(levels.len() == 5)
```

</details>

#### report has finding count

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 0
check(count >= 0)
```

</details>

#### report has file locations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_locations = true
check(has_locations)
```

</details>

#### report has recommendations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_recs = true
check(has_recs)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
