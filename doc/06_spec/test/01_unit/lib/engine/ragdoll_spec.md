# Ragdoll Specification

> 1. var rd = Ragdoll new

<!-- sdn-diagram:id=ragdoll_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ragdoll_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ragdoll_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ragdoll_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ragdoll Specification

## Scenarios

### Ragdoll

#### creates empty ragdoll

1. var rd = Ragdoll new
   - Expected: rd.name equals `humanoid`
   - Expected: rd.bone_count() equals `0`
   - Expected: rd.joint_count() equals `0`
   - Expected: rd.is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("humanoid")
expect(rd.name).to_equal("humanoid")
expect(rd.bone_count()).to_equal(0)
expect(rd.joint_count()).to_equal(0)
expect(rd.is_active()).to_equal(false)
```

</details>

#### adds bones

1. var rd = Ragdoll new
   - Expected: rd.bone_count() equals `2`
   - Expected: i0 equals `0`
   - Expected: i1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
val i0 = rd.add_bone("spine", 0, 100, 5.0, 0.4)
val i1 = rd.add_bone("head", 1, 101, 3.0, 0.2)
expect(rd.bone_count()).to_equal(2)
expect(i0).to_equal(0)
expect(i1).to_equal(1)
```

</details>

#### retrieves bone by index

1. var rd = Ragdoll new
2. rd add bone
   - Expected: b.name equals `torso`
   - Expected: b.mass equals `10.0`
   - Expected: "bone missing" equals `bone found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
rd.add_bone("torso", 0, 50, 10.0, 0.5)
if val Some(b) = rd.get_bone(0):
    expect(b.name).to_equal("torso")
    expect(b.mass).to_equal(10.0)
else:
    expect("bone missing").to_equal("bone found")
```

</details>

#### returns nil for invalid bone index

1. var rd = Ragdoll new
   - Expected: rd.bone_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
val result = rd.get_bone(99)
# Can't use to_be_nil; check bone_count instead
expect(rd.bone_count()).to_equal(0)
```

</details>

#### adds joints

1. var rd = Ragdoll new
2. rd add bone
3. rd add bone
   - Expected: rd.joint_count() equals `1`
   - Expected: ji equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
rd.add_bone("a", 0, 1, 5.0, 0.3)
rd.add_bone("b", 1, 2, 3.0, 0.2)
val ji = rd.add_joint(0, 1, -45.0, 45.0)
expect(rd.joint_count()).to_equal(1)
expect(ji).to_equal(0)
```

</details>

#### activates and deactivates

1. var rd = Ragdoll new
   - Expected: rd.is_active() is false
2. rd activate
   - Expected: rd.is_active() is true
3. rd deactivate
   - Expected: rd.is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
expect(rd.is_active()).to_equal(false)
rd.activate()
expect(rd.is_active()).to_equal(true)
rd.deactivate()
expect(rd.is_active()).to_equal(false)
```

</details>

#### computes total mass

1. var rd = Ragdoll new
2. rd add bone
3. rd add bone
4. rd add bone
   - Expected: rd.total_mass() equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("test")
rd.add_bone("a", 0, 1, 5.0, 0.3)
rd.add_bone("b", 1, 2, 3.0, 0.2)
rd.add_bone("c", 2, 3, 2.0, 0.1)
expect(rd.total_mass()).to_equal(10.0)
```

</details>

#### total mass of empty ragdoll is zero

1. var rd = Ragdoll new
   - Expected: rd.total_mass() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rd = Ragdoll.new("empty")
expect(rd.total_mass()).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/ragdoll_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ragdoll

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
