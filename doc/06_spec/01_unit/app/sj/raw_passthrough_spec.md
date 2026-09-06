# Raw Passthrough Specification

> <details>

<!-- sdn-diagram:id=raw_passthrough_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=raw_passthrough_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

raw_passthrough_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=raw_passthrough_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raw Passthrough Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/raw_passthrough_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Raw Passthrough - sj raw jj

#### passes through raw jj commands with shared lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["raw", "jj", "op", "log"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("jj op log")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### passes through raw git commands with exclusive lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["raw", "git", "gc"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git gc")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

### Raw Passthrough - LFS

#### routes git lfs as raw passthrough with shared lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "lfs", "pull"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git lfs pull")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

### Raw Passthrough - Clean

#### routes git clean as raw passthrough with warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "clean", "-fd"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git clean -fd")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(plan.warning).to_contain("WARN")
```

</details>

### Raw Passthrough - Unknown Verb

#### treats unknown git verbs as direct jj commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "unknown-verb", "arg1"])
expect(plan.classification).to_equal("direct_jj")
expect(plan.commands[0i64]).to_contain("jj")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
