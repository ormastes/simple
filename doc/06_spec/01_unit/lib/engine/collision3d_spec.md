# collision3d_spec

> Engine Collision 3D — Narrow-phase 3D collision detection tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# collision3d_spec

Engine Collision 3D — Narrow-phase 3D collision detection tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/collision3d_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Collision 3D — Narrow-phase 3D collision detection tests

Tests sphere-sphere, AABB-AABB, sphere-AABB, and OBB-OBB collision
detection functions. Uses the pure Simple 3D collision module.

## Scenarios

### Collision3D sphere-sphere

#### overlapping returns contact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- overlapping returns contact
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overlapping returns contact")
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 1.5, y: 0.0, z: 0.0), 1.0
)
# In interpreter Option::Some(x) unwraps to x directly
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    val pen = contact.penetration * 100.0
    expect(pen).to_be_greater_than(49.0)
    expect(pen).to_be_less_than(51.0)
```

</details>

#### non-overlapping returns nil

- non-overlapping returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-overlapping returns nil")
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 5.0, y: 0.0, z: 0.0), 1.0
)
expect(contact).to_be_nil()
```

</details>

### Collision3D AABB-AABB

#### overlapping returns contact

- overlapping returns contact
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overlapping returns contact")
val contact = collide_aabb_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0),
    Vec3(x: 1.5, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### separated returns nil

- separated returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separated returns nil")
val contact = collide_aabb_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0),
    Vec3(x: 5.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
expect(contact).to_be_nil()
```

</details>

### Collision3D sphere-AABB

#### sphere inside box

- sphere inside box
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sphere inside box")
val contact = collide_sphere_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 0.5,
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 2.0, y: 2.0, z: 2.0)
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### sphere outside box

- sphere outside box


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sphere outside box")
val contact = collide_sphere_aabb(
    Vec3(x: 10.0, y: 0.0, z: 0.0), 0.5,
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
expect(contact).to_be_nil()
```

</details>

### Collision3D OBB-OBB

#### aligned boxes overlap

- aligned boxes overlap
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aligned boxes overlap")
# OBB with identity rotation = AABB
val identity = Quaternion.identity()
val contact = collide_obb_obb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity,
    Vec3(x: 1.5, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### separated boxes

- separated boxes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separated boxes")
val identity = Quaternion.identity()
val contact = collide_obb_obb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity,
    Vec3(x: 10.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity
)
expect(contact).to_be_nil()
```

</details>

### Collision3D contact normal

#### contact normal points from A to B

- contact normal points from A to B
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contact normal points from A to B")
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 1.0, y: 0.0, z: 0.0), 1.0
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    # Normal should point from A to B, so x > 0
    expect(contact.normal.x).to_be_greater_than(0.0)
    # Y and Z should be approximately zero
    val ny_i = contact.normal.y * 1000.0
    val nz_i = contact.normal.z * 1000.0
    expect(ny_i).to_be_greater_than(-1.0)
    expect(ny_i).to_be_less_than(1.0)
    expect(nz_i).to_be_greater_than(-1.0)
    expect(nz_i).to_be_less_than(1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f10775de35f883c24b60f746aaa2a3a699644247bb1f3fb75a21bbf67023e667`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f10775de35f883c24b60f746aaa2a3a699644247bb1f3fb75a21bbf67023e667`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f10775de35f883c24b60f746aaa2a3a699644247bb1f3fb75a21bbf67023e667`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/engine/collision3d_spec.spl
mirror: doc/06_spec/01_unit/lib/engine/collision3d_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/engine/collision3d_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/engine/collision3d_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/engine/collision3d_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overlapping returns contact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/collision3d_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-overlapping returns nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/collision3d_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overlapping returns contact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
