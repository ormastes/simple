# Direct JJ Translation Specification

> <details>

<!-- sdn-diagram:id=direct_jj_translation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direct_jj_translation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direct_jj_translation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direct_jj_translation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct JJ Translation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/direct_jj_translation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Direct JJ Translation - Read Verbs

#### translates git status to jj status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "status"])
expect(plan.commands[0i64]).to_equal("jj status")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
expect(plan.classification).to_equal("direct_jj")
```

</details>

#### translates git log to jj log

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "log"])
expect(plan.commands[0i64]).to_equal("jj log")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git diff to jj diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "diff"])
expect(plan.commands[0i64]).to_equal("jj diff")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git blame to jj file annotate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "blame", "src/main.spl"])
expect(plan.commands[0i64]).to_equal("jj file annotate src/main.spl")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git branch --list to jj bookmark list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "branch", "--list"])
expect(plan.commands[0i64]).to_equal("jj bookmark list")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

### Direct JJ Translation - Mutating Verbs

#### translates git checkout <rev> to jj new <rev>

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["git", "checkout", "abc123"])
expect(plan.commands[0i64]).to_equal("jj new abc123")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### passes through jj-native verbs with exclusive lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = translate(["describe", "-m", "test message"])
expect(plan.commands[0i64]).to_equal("jj describe -m test message")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(plan.classification).to_equal("direct_jj")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
