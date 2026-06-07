# Address Space Specification

> _Fresh handle allocation._

<!-- sdn-diagram:id=address_space_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=address_space_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

address_space_spec -> std
address_space_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=address_space_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Address Space Specification

## Scenarios

### vmm per-process address space

### create_user_address_space
_Fresh handle allocation._

#### returns the legacy sentinel phys_root when PMM is offline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = create_user_address_space()
expect(_is_sentinel(space.phys_root)).to_equal(1)
```

</details>

#### returns id 0 for every sentinel handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = create_user_address_space()
expect(space.id).to_equal(0)
```

</details>

#### produces a handle whose phys_root stays stable across reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = create_user_address_space()
val first = space.phys_root
val second = space.phys_root
expect(second).to_equal(first)
```

</details>

### destroy_user_address_space
_Cleanup path accepts freshly-created handles._

#### leaves the caller's phys_root field value unchanged

1. destroy user address space
   - Expected: space.phys_root equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = create_user_address_space()
val before = space.phys_root
destroy_user_address_space(space)
expect(space.phys_root).to_equal(before)
```

</details>

#### leaves the caller's id field unchanged

1. destroy user address space
   - Expected: space.id equals `before_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = create_user_address_space()
val before_id = space.id
destroy_user_address_space(space)
expect(space.id).to_equal(before_id)
```

</details>

#### is a no-op on the legacy sentinel

1. destroy user address space
   - Expected: sentinel.phys_root equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sentinel = AddressSpace(phys_root: 1, id: 0)
destroy_user_address_space(sentinel)
expect(sentinel.phys_root).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/memory/address_space_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vmm per-process address space
- create_user_address_space
- destroy_user_address_space

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
