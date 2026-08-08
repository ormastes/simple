# PhysicsWorld2D collision filters + triggers

> `PhysicsWorld2D.detect_contacts()` must honor two per-collider settings that gameplay code relies on: a `CollisionFilter` (category/mask bits) that can suppress contact generation entirely between two overlapping shapes, and an `is_sensor` flag that turns a solid contact into a non-physical trigger event (the shapes overlap freely; only an event fires, bodies are never pushed apart). This spec proves both settings are respected, that they compose correctly with default (unfiltered, non-trigger) behavior, and that they hold on BOTH broadphase paths — the brute-force path used for <=4 colliders and the BVH path used above that threshold — since [C11] was a regression where the BVH path silently dropped this wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PhysicsWorld2D collision filters + triggers

`PhysicsWorld2D.detect_contacts()` must honor two per-collider settings that gameplay code relies on: a `CollisionFilter` (category/mask bits) that can suppress contact generation entirely between two overlapping shapes, and an `is_sensor` flag that turns a solid contact into a non-physical trigger event (the shapes overlap freely; only an event fires, bodies are never pushed apart). This spec proves both settings are respected, that they compose correctly with default (unfiltered, non-trigger) behavior, and that they hold on BOTH broadphase paths — the brute-force path used for <=4 colliders and the BVH path used above that threshold — since [C11] was a regression where the BVH path silently dropped this wiring.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/world2d_filter_trigger_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`PhysicsWorld2D.detect_contacts()` must honor two per-collider settings
that gameplay code relies on: a `CollisionFilter` (category/mask bits)
that can suppress contact generation entirely between two overlapping
shapes, and an `is_sensor` flag that turns a solid contact into a
non-physical trigger event (the shapes overlap freely; only an event
fires, bodies are never pushed apart). This spec proves both settings are
respected, that they compose correctly with default (unfiltered,
non-trigger) behavior, and that they hold on BOTH broadphase paths — the
brute-force path used for <=4 colliders and the BVH path used above that
threshold — since [C11] was a regression where the BVH path silently
dropped this wiring.

## Examples

Two default-filtered overlapping dynamic bodies produce exactly one solid
contact and zero trigger events (baseline). Giving them incompatible
category/mask filters drops the contact to zero and leaves both bodies'
positions unmoved. Marking one collider `is_sensor` instead produces zero
solid contacts, exactly one trigger event, and still leaves positions
unmoved (a trigger never separates bodies). A 6-collider scene (past the
4-collider BVH threshold) runs all three pairings — trigger, masked-out,
and default-solid — simultaneously and proves the BVH path resolves each
pair identically to the brute-force path.

## Scenarios

### PhysicsWorld2D collision filters + triggers

#### backward compat: default filters/no-trigger produce the same contact as unfiltered behavior

- Overlap two default-filtered dynamic circles
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
- world step
- Default settings must produce one solid contact and no trigger events
   - Expected: world.contact_count() equals `1`
   - Expected: world.get_trigger_events().len() equals `0`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Overlap two default-filtered dynamic circles")
var world = PhysicsWorld2D.create(zero_gravity_config())
val a = make_node(1)
val b = make_node(2)
world.add_dynamic_body(a, 0.0, 0.0, 1.0)
world.add_circle_collider(a, 0.3)
world.add_dynamic_body(b, 0.2, 0.0, 1.0)
world.add_circle_collider(b, 0.3)
world.step(world.config.fixed_timestep)
step("Default settings must produce one solid contact and no trigger events")
expect(world.contact_count()).to_equal(1)
expect(world.get_trigger_events().len()).to_equal(0)
world.destroy()
```

</details>

#### masks-reject-pair: an incompatible category/mask pair produces NO contact

- Overlap two circles with incompatible category/mask filters
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
- world set collider filter
- world set collider filter
- world step
- The filter must suppress the contact entirely and leave both bodies unmoved
   - Expected: world.contact_count() equals `0`
   - Expected: pos_a_after.x equals `pos_a_before.x`
   - Expected: pos_a_after.y equals `pos_a_before.y`
   - Expected: pos_b_after.x equals `pos_b_before.x`
   - Expected: pos_b_after.y equals `pos_b_before.y`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Overlap two circles with incompatible category/mask filters")
var world = PhysicsWorld2D.create(zero_gravity_config())
val a = make_node(1)
val b = make_node(2)
world.add_dynamic_body(a, 0.0, 0.0, 1.0)
world.add_circle_collider(a, 0.3)
world.add_dynamic_body(b, 0.2, 0.0, 1.0)
world.add_circle_collider(b, 0.3)
world.set_collider_filter(a, CollisionFilter.with_mask(2, 2))
world.set_collider_filter(b, CollisionFilter.with_mask(4, 1))
val pos_a_before = world.get_position(a)
val pos_b_before = world.get_position(b)
world.step(world.config.fixed_timestep)
step("The filter must suppress the contact entirely and leave both bodies unmoved")
expect(world.contact_count()).to_equal(0)
val pos_a_after = world.get_position(a)
val pos_b_after = world.get_position(b)
expect(pos_a_after.x).to_equal(pos_a_before.x)
expect(pos_a_after.y).to_equal(pos_a_before.y)
expect(pos_b_after.x).to_equal(pos_b_before.x)
expect(pos_b_after.y).to_equal(pos_b_before.y)
world.destroy()
```

</details>

#### trigger-pair: an is_sensor collider emits a trigger event and does not push bodies apart

- Overlap two circles, marking one as a sensor (trigger)
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
- world set trigger
- world step
- A sensor pair must fire a trigger event with zero solid contacts and no separation
   - Expected: world.contact_count() equals `0`
   - Expected: world.get_trigger_events().len() equals `1`
   - Expected: pos_a_after.x equals `pos_a_before.x`
   - Expected: pos_a_after.y equals `pos_a_before.y`
   - Expected: pos_b_after.x equals `pos_b_before.x`
   - Expected: pos_b_after.y equals `pos_b_before.y`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Overlap two circles, marking one as a sensor (trigger)")
var world = PhysicsWorld2D.create(zero_gravity_config())
val a = make_node(1)
val b = make_node(2)
world.add_dynamic_body(a, 0.0, 0.0, 1.0)
world.add_circle_collider(a, 0.3)
world.add_dynamic_body(b, 0.2, 0.0, 1.0)
world.add_circle_collider(b, 0.3)
world.set_trigger(b, true)
val pos_a_before = world.get_position(a)
val pos_b_before = world.get_position(b)
world.step(world.config.fixed_timestep)
step("A sensor pair must fire a trigger event with zero solid contacts and no separation")
expect(world.contact_count()).to_equal(0)
expect(world.get_trigger_events().len()).to_equal(1)
val pos_a_after = world.get_position(a)
val pos_b_after = world.get_position(b)
expect(pos_a_after.x).to_equal(pos_a_before.x)
expect(pos_a_after.y).to_equal(pos_a_before.y)
expect(pos_b_after.x).to_equal(pos_b_before.x)
expect(pos_b_after.y).to_equal(pos_b_before.y)
world.destroy()
```

</details>

#### BVH broadphase path (>4 colliders) applies the same filter/trigger wiring

- Build 6 colliders (past the 4-collider BVH threshold): one trigger pair, one masked-out pair, one default-solid pair
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
- world set trigger
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
- world set collider filter
- world set collider filter
- world add dynamic body
- world add circle collider
- world add dynamic body
- world add circle collider
   - Expected: world.colliders.count > 4 is true
- world step
- Each pair must resolve identically to the brute-force path: 1 solid contact, 1 trigger, e/f pushed apart
   - Expected: world.contact_count() equals `1`
   - Expected: world.get_trigger_events().len() equals `1`
   - Expected: e_f_differ is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build 6 colliders (past the 4-collider BVH threshold): one trigger pair, one masked-out pair, one default-solid pair")
var world = PhysicsWorld2D.create(zero_gravity_config())
val a = make_node(1)
val b = make_node(2)
val c = make_node(3)
val d = make_node(4)
val e = make_node(5)
val f = make_node(6)
# pair (a,b): trigger — overlapping, b is a sensor
world.add_dynamic_body(a, 0.0, 0.0, 1.0)
world.add_circle_collider(a, 0.3)
world.add_dynamic_body(b, 0.2, 0.0, 1.0)
world.add_circle_collider(b, 0.3)
world.set_trigger(b, true)
# pair (c,d): masked-out — overlapping, incompatible category/mask
world.add_dynamic_body(c, 10.0, 0.0, 1.0)
world.add_circle_collider(c, 0.3)
world.add_dynamic_body(d, 10.2, 0.0, 1.0)
world.add_circle_collider(d, 0.3)
world.set_collider_filter(c, CollisionFilter.with_mask(2, 2))
world.set_collider_filter(d, CollisionFilter.with_mask(4, 1))
# pair (e,f): default — overlapping, solid contact expected
world.add_dynamic_body(e, 20.0, 0.0, 1.0)
world.add_circle_collider(e, 0.3)
world.add_dynamic_body(f, 20.2, 0.0, 1.0)
world.add_circle_collider(f, 0.3)
# 6 colliders > 4 => detect_contacts() routes through detect_contacts_bvh()
expect(world.colliders.count > 4).to_equal(true)
world.step(world.config.fixed_timestep)
step("Each pair must resolve identically to the brute-force path: 1 solid contact, 1 trigger, e/f pushed apart")
expect(world.contact_count()).to_equal(1)
expect(world.get_trigger_events().len()).to_equal(1)
val pos_e = world.get_position(e)
val pos_f = world.get_position(f)
val e_f_differ = pos_e.x != pos_f.x
expect(e_f_differ).to_equal(true)
world.destroy()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
