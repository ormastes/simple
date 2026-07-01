# Multi-Step Translation Specification

> <details>

<!-- sdn-diagram:id=multi_step_translation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_step_translation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_step_translation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_step_translation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Step Translation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/multi_step_translation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Multi-Step Translation - Commit

#### translates git commit -m to describe + new

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "commit", "-m", "my message"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_contain("jj describe")
expect(plan.commands[1i64]).to_equal("jj new")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### translates git commit --amend to describe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "commit", "--amend"])
expect(plan.classification).to_equal("direct_jj")
expect(plan.commands[0i64]).to_contain("jj describe")
```

</details>

### Multi-Step Translation - Checkout -b

#### translates git checkout -b to new + bookmark create

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "checkout", "-b", "feature-x"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_equal("jj new")
expect(plan.commands[1i64]).to_contain("bookmark create feature-x")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### translates git checkout -b with base to new <base> + bookmark

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "checkout", "-b", "feature-y", "main"])
expect(plan.commands[0i64]).to_equal("jj new main")
expect(plan.commands[1i64]).to_contain("bookmark create feature-y")
```

</details>

### Multi-Step Translation - Pull

#### translates git pull to fetch + rebase

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "pull"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_equal("jj git fetch")
expect(plan.commands[1i64]).to_equal("jj rebase -d main@origin")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

### Multi-Step Translation - Lease Sharing

#### all multi-step commands use exclusive leases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commit_plan = translate(["git", "commit", "-m", "x"])
val pull_plan = translate(["git", "pull"])
val branch_plan = translate(["git", "checkout", "-b", "test"])
expect(commit_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(pull_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(branch_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
