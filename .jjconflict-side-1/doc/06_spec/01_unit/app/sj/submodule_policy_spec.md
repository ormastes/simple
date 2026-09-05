# Submodule Policy Specification

> <details>

<!-- sdn-diagram:id=submodule_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=submodule_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

submodule_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=submodule_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Submodule Policy Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/submodule_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Submodule Policy - Detection

#### detects git submodule add

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "add", "https://example.com/repo", "vendor/lib"])
expect(plan.is_submodule).to_equal(true)
```

</details>

#### detects git submodule status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.is_submodule).to_equal(true)
```

</details>

#### does not flag non-submodule git commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "status"])
expect(plan.is_submodule).to_equal(false)
```

</details>

#### does not flag non-git commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["describe", "-m", "test"])
expect(plan.is_submodule).to_equal(false)
```

</details>

### Submodule Policy - Exclusive Lease

#### submodule add uses exclusive lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "add", "url", "path"])
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### submodule status uses shared lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### submodule update uses exclusive lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "update"])
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

### Submodule Policy - Warning

#### submodule add produces WARN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "add", "url", "vendor/lib"])
expect(plan.warning).to_contain("WARN[SUBMODULE]")
expect(plan.warning).to_contain("gitlink")
```

</details>

#### submodule status has no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.warning).to_equal("")
```

</details>

### Submodule Policy - Auto-Pin

#### submodule add produces auto-pin command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "add", "url", "vendor/lib"])
expect(plan.auto_pin_cmd).to_contain("git commit")
expect(plan.auto_pin_cmd).to_contain("pin submodule vendor/lib")
```

</details>

#### submodule status has no auto-pin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.auto_pin_cmd).to_equal("")
```

</details>

### Submodule Policy - Read Negative

#### short argv returns non-submodule

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule(["git"])
expect(plan.is_submodule).to_equal(false)
```

</details>

#### empty argv returns non-submodule

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = classify_submodule([])
expect(plan.is_submodule).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
