# Rapier2D SFFI Implementation Guide

**Status**: SFFI wrapper complete, Rust runtime implementation needed
**Created**: 2026-02-08
**Files**:
- SFFI Wrapper: `src/app/io/rapier2d_ffi.spl` (~620 lines)
- Test Spec: `test/app/io/rapier2d_ffi_spec.spl` (~360 lines)
- Demo: `examples/physics_rapier2d_demo.spl` (~120 lines)

## Overview

This guide explains how to implement the Rust runtime side of the Rapier2D physics engine SFFI wrapper for the Simple language compiler.

The Simple-side wrapper is **complete** and follows the two-tier SFFI pattern used throughout the project. This document covers the Rust implementation needed to make the wrapper functional.

## Architecture

### Two-Tier SFFI Pattern

**Tier 1: Extern Declarations** (Simple)
```simple
extern fn rt_rapier2d_world_new(gravity_x: f64, gravity_y: f64) -> i64
extern fn rt_rapier2d_body_new_dynamic(world: i64, x: f64, y: f64, rotation: f64) -> i64
```

**Tier 2: Simple Wrappers** (Simple)
```simple
fn physics_create_world(gravity: Vector2) -> PhysicsWorld:
    val handle = rt_rapier2d_world_new(gravity.x, gravity.y)
    PhysicsWorld(handle: handle, is_valid: handle != 0)
```

**Runtime Implementation** (Rust - to be implemented)
```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_world_new(gravity_x: f64, gravity_y: f64) -> i64 {
    // Implementation here
}
```

## Rust Dependencies

Add to runtime's `Cargo.toml`:

```toml
[dependencies]
rapier2d = "0.17"  # Or latest version
nalgebra = "0.32"  # Required by Rapier
```

## Implementation Strategy

### 1. Handle Management

Rapier uses typed handles internally, but we expose opaque `i64` handles to Simple. We need a handle manager:

```rust
use std::collections::HashMap;
use std::sync::Mutex;
use rapier2d::prelude::*;

// Global state (thread-safe)
lazy_static! {
    static ref PHYSICS_WORLDS: Mutex<HashMap<i64, PhysicsWorld2D>> = Mutex::new(HashMap::new());
    static ref NEXT_WORLD_ID: Mutex<i64> = Mutex::new(1);
}

struct PhysicsWorld2D {
    gravity: Vector<f64>,
    integration_params: IntegrationParameters,
    physics_pipeline: PhysicsPipeline,
    island_manager: IslandManager,
    broad_phase: BroadPhase,
    narrow_phase: NarrowPhase,
    impulse_joint_set: ImpulseJointSet,
    multibody_joint_set: MultibodyJointSet,
    ccd_solver: CCDSolver,
    rigid_body_set: RigidBodySet,
    collider_set: ColliderSet,
    query_pipeline: QueryPipeline,
}

impl PhysicsWorld2D {
    fn new(gravity: Vector<f64>) -> Self {
        Self {
            gravity,
            integration_params: IntegrationParameters::default(),
            physics_pipeline: PhysicsPipeline::new(),
            island_manager: IslandManager::new(),
            broad_phase: BroadPhase::new(),
            narrow_phase: NarrowPhase::new(),
            impulse_joint_set: ImpulseJointSet::new(),
            multibody_joint_set: MultibodyJointSet::new(),
            ccd_solver: CCDSolver::new(),
            rigid_body_set: RigidBodySet::new(),
            collider_set: ColliderSet::new(),
            query_pipeline: QueryPipeline::new(),
        }
    }

    fn step(&mut self, dt: f64) {
        self.integration_params.dt = dt as f32;

        self.physics_pipeline.step(
            &self.gravity,
            &self.integration_params,
            &mut self.island_manager,
            &mut self.broad_phase,
            &mut self.narrow_phase,
            &mut self.rigid_body_set,
            &mut self.collider_set,
            &mut self.impulse_joint_set,
            &mut self.multibody_joint_set,
            &mut self.ccd_solver,
            None, // physics hooks
            &(), // event handler
        );

        self.query_pipeline.update(&self.rigid_body_set, &self.collider_set);
    }
}
```

### 2. World Management Functions

```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_world_new(gravity_x: f64, gravity_y: f64) -> i64 {
    let gravity = Vector::new(gravity_x as f32, gravity_y as f32);
    let world = PhysicsWorld2D::new(gravity);

    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    let mut next_id = NEXT_WORLD_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    worlds.insert(id, world);
    id
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_world_free(world_id: i64) -> bool {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    worlds.remove(&world_id).is_some()
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_world_step(world_id: i64, dt: f64) -> bool {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        world.step(dt);
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_world_set_gravity(world_id: i64, x: f64, y: f64) -> bool {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        world.gravity = Vector::new(x as f32, y as f32);
        true
    } else {
        false
    }
}
```

### 3. Rigid Body Functions

```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_body_new_dynamic(
    world_id: i64,
    x: f64,
    y: f64,
    rotation: f64,
) -> i64 {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let rigid_body = RigidBodyBuilder::dynamic()
            .translation(Vector::new(x as f32, y as f32))
            .rotation(rotation as f32)
            .build();

        let handle = world.rigid_body_set.insert(rigid_body);

        // Convert RigidBodyHandle to i64
        // Rapier uses 32-bit handles internally
        encode_rigid_body_handle(handle)
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_body_new_static(
    world_id: i64,
    x: f64,
    y: f64,
    rotation: f64,
) -> i64 {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let rigid_body = RigidBodyBuilder::fixed()
            .translation(Vector::new(x as f32, y as f32))
            .rotation(rotation as f32)
            .build();

        let handle = world.rigid_body_set.insert(rigid_body);
        encode_rigid_body_handle(handle)
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_body_get_position(
    world_id: i64,
    body_handle: i64,
) -> (f64, f64, f64) {
    let worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get(&world_id) {
        let handle = decode_rigid_body_handle(body_handle);
        if let Some(body) = world.rigid_body_set.get(handle) {
            let pos = body.translation();
            let rot = body.rotation();
            return (pos.x as f64, pos.y as f64, rot.angle() as f64);
        }
    }
    (0.0, 0.0, 0.0)
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_body_apply_force(
    world_id: i64,
    body_handle: i64,
    fx: f64,
    fy: f64,
    wake_up: bool,
) -> bool {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let handle = decode_rigid_body_handle(body_handle);
        if let Some(body) = world.rigid_body_set.get_mut(handle) {
            let force = Vector::new(fx as f32, fy as f32);
            body.add_force(force, wake_up);
            return true;
        }
    }
    false
}
```

### 4. Handle Encoding/Decoding

Rapier uses typed handles internally. We need to convert to/from `i64`:

```rust
use rapier2d::prelude::{RigidBodyHandle, ColliderHandle};

fn encode_rigid_body_handle(handle: RigidBodyHandle) -> i64 {
    // RigidBodyHandle contains a u32 index
    // We'll use the lower 32 bits for the index
    // and upper 32 bits for a type tag (1 = rigid body)
    let index = handle.into_raw_parts().0;
    ((1i64) << 32) | (index as i64)
}

fn decode_rigid_body_handle(encoded: i64) -> RigidBodyHandle {
    let index = (encoded & 0xFFFFFFFF) as u32;
    RigidBodyHandle::from_raw_parts(index, 0)
}

fn encode_collider_handle(handle: ColliderHandle) -> i64 {
    let index = handle.into_raw_parts().0;
    ((2i64) << 32) | (index as i64)  // Type tag 2 = collider
}

fn decode_collider_handle(encoded: i64) -> ColliderHandle {
    let index = (encoded & 0xFFFFFFFF) as u32;
    ColliderHandle::from_raw_parts(index, 0)
}
```

### 5. Collider Functions

```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_collider_new_circle(
    world_id: i64,
    body_handle: i64,
    radius: f64,
) -> i64 {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let parent = decode_rigid_body_handle(body_handle);

        let collider = ColliderBuilder::ball(radius as f32)
            .build();

        let handle = world.collider_set.insert_with_parent(
            collider,
            parent,
            &mut world.rigid_body_set,
        );

        encode_collider_handle(handle)
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_collider_new_box(
    world_id: i64,
    body_handle: i64,
    half_width: f64,
    half_height: f64,
) -> i64 {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let parent = decode_rigid_body_handle(body_handle);

        let collider = ColliderBuilder::cuboid(half_width as f32, half_height as f32)
            .build();

        let handle = world.collider_set.insert_with_parent(
            collider,
            parent,
            &mut world.rigid_body_set,
        );

        encode_collider_handle(handle)
    } else {
        0
    }
}
```

### 6. Collision Detection Functions

```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_world_get_contacts(world_id: i64) -> i64 {
    // Return a handle to a ContactList structure
    // This needs a separate contact list manager
    // For now, we'll use a simple approach
    0 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_world_intersection_test(
    world_id: i64,
    collider1: i64,
    collider2: i64,
) -> bool {
    let worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get(&world_id) {
        let h1 = decode_collider_handle(collider1);
        let h2 = decode_collider_handle(collider2);

        if let (Some(c1), Some(c2)) = (
            world.collider_set.get(h1),
            world.collider_set.get(h2),
        ) {
            // Use the query pipeline for intersection test
            return world.query_pipeline.intersection_with_shape(
                &world.rigid_body_set,
                &world.collider_set,
                c1.position(),
                c1.shape(),
                Default::default(),
            ).is_some();
        }
    }
    false
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_world_cast_ray(
    world_id: i64,
    origin_x: f64,
    origin_y: f64,
    dir_x: f64,
    dir_y: f64,
    max_dist: f64,
) -> (bool, i64, f64) {
    let worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get(&world_id) {
        let ray = Ray::new(
            Point::new(origin_x as f32, origin_y as f32),
            Vector::new(dir_x as f32, dir_y as f32),
        );

        if let Some((handle, toi)) = world.query_pipeline.cast_ray(
            &world.rigid_body_set,
            &world.collider_set,
            &ray,
            max_dist as f32,
            true,
            Default::default(),
        ) {
            return (true, encode_collider_handle(handle), toi as f64);
        }
    }
    (false, 0, 0.0)
}
```

### 7. Joint Functions

```rust
#[no_mangle]
pub extern "C" fn rt_rapier2d_joint_revolute(
    world_id: i64,
    body1: i64,
    body2: i64,
    anchor_x: f64,
    anchor_y: f64,
) -> i64 {
    let mut worlds = PHYSICS_WORLDS.lock().unwrap();
    if let Some(world) = worlds.get_mut(&world_id) {
        let h1 = decode_rigid_body_handle(body1);
        let h2 = decode_rigid_body_handle(body2);

        let joint = RevoluteJointBuilder::new()
            .local_anchor1(Point::new(anchor_x as f32, anchor_y as f32))
            .local_anchor2(Point::new(0.0, 0.0))
            .build();

        let handle = world.impulse_joint_set.insert(h1, h2, joint, true);
        encode_joint_handle(handle)
    } else {
        0
    }
}
```

## Integration with Simple Runtime

### Location

Add the implementation to the runtime's FFI module:
- **Path**: `bin/runtime/src/ffi/physics.rs` (new file)
- **Add to**: `bin/runtime/src/ffi/mod.rs`

### Module Structure

```rust
// bin/runtime/src/ffi/mod.rs
pub mod physics;  // Add this

// bin/runtime/src/ffi/physics.rs
mod rapier2d;  // The implementation above

pub use rapier2d::*;
```

## Testing Strategy

### 1. Unit Tests (Rust)

Add Rust tests for handle encoding/decoding:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_encoding() {
        let original = RigidBodyHandle::from_raw_parts(42, 0);
        let encoded = encode_rigid_body_handle(original);
        let decoded = decode_rigid_body_handle(encoded);
        assert_eq!(original, decoded);
    }
}
```

### 2. Integration Tests (Simple)

Run the test spec:

```bash
bin/simple test test/app/io/rapier2d_ffi_spec.spl
```

### 3. Demo Test

Run the demo:

```bash
bin/simple examples/physics_rapier2d_demo.spl
```

## Performance Considerations

### Memory Management

- **World Cleanup**: Ensure worlds are properly cleaned up when freed
- **Handle Reuse**: Consider handle recycling for long-running simulations
- **Thread Safety**: Use `Mutex` for global state, consider `RwLock` for read-heavy workloads

### Optimization

- **Integration Parameters**: Tune timestep and iterations
- **Broad Phase**: Configure spatial hash grid size for your use case
- **CCD**: Enable/disable continuous collision detection as needed

```rust
impl PhysicsWorld2D {
    fn new_optimized(gravity: Vector<f64>) -> Self {
        let mut integration_params = IntegrationParameters::default();
        integration_params.dt = 1.0 / 60.0;  // 60 FPS
        integration_params.max_ccd_substeps = 1;  // Reduce for performance

        Self {
            gravity,
            integration_params,
            // ... rest
        }
    }
}
```

## Error Handling

### Current Approach

The SFFI wrapper returns `false` or `0` handles on error. Consider adding:

```rust
thread_local! {
    static LAST_ERROR: RefCell<String> = RefCell::new(String::new());
}

#[no_mangle]
pub extern "C" fn rt_rapier2d_get_last_error() -> *const c_char {
    LAST_ERROR.with(|e| {
        let error = e.borrow();
        CString::new(error.as_str()).unwrap().into_raw()
    })
}

fn set_error(msg: &str) {
    LAST_ERROR.with(|e| {
        *e.borrow_mut() = msg.to_string();
    });
}
```

## Example Implementation Checklist

- [ ] Add `rapier2d` to runtime `Cargo.toml`
- [ ] Create `bin/runtime/src/ffi/physics.rs`
- [ ] Implement world management (new, free, step, set_gravity)
- [ ] Implement rigid body functions (new, position, velocity, forces)
- [ ] Implement collider functions (shapes, materials, sensors)
- [ ] Implement collision detection (contacts, intersection, raycast)
- [ ] Implement joints (distance, revolute, prismatic, fixed)
- [ ] Add handle encoding/decoding
- [ ] Add error handling
- [ ] Write Rust unit tests
- [ ] Run Simple integration tests
- [ ] Test demo example
- [ ] Profile and optimize

## Next Steps

1. **Implement Core Functions**: Start with world + rigid body + collider
2. **Test Basic Simulation**: Get the demo running
3. **Add Collision Detection**: Implement contact queries
4. **Add Joints**: Implement constraint system
5. **Optimize**: Tune performance for target use cases

## References

- **Rapier Documentation**: https://rapier.rs/docs/
- **Rapier2D API**: https://docs.rs/rapier2d/
- **Simple SFFI Pattern**: `src/app/io/vulkan_ffi.spl` (reference implementation)
- **Handle Management**: Similar to Vulkan handles in Simple runtime

## Summary

The Simple-side SFFI wrapper is complete (~620 lines) and provides a comprehensive 2D physics API. The Rust runtime implementation requires:

1. **~800-1000 lines** of Rust code
2. **Rapier2D dependency** (~500KB compiled)
3. **Handle management** for opaque i64 handles
4. **Thread-safe global state** for world storage

Once implemented, Simple programs will have access to a production-ready 2D physics engine with rigid bodies, colliders, joints, and collision detection.
