use crate::error::CompileError;
use crate::value::Value;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::LazyLock;

use super::common::error_utils::{unknown_function, wrong_arg_type};

static NEXT_WORLD_ID: AtomicI64 = AtomicI64::new(1);
static NEXT_CONTACT_LIST_ID: AtomicI64 = AtomicI64::new(1);
static WORLDS: LazyLock<Mutex<HashMap<i64, PhysicsWorldState>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static CONTACT_LISTS: LazyLock<Mutex<HashMap<i64, Vec<ContactRecord>>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

#[derive(Clone)]
struct BodyState {
    body_type: i64,
    x: f64,
    y: f64,
    rotation: f64,
    vx: f64,
    vy: f64,
    angular_velocity: f64,
    force_x: f64,
    force_y: f64,
    mass: f64,
    linear_damping: f64,
    angular_damping: f64,
    sleeping: bool,
}

#[derive(Clone)]
enum ColliderShape {
    Circle { radius: f64 },
    Box { half_width: f64, half_height: f64 },
    Capsule { half_height: f64, radius: f64 },
    Polygon { vertices: Vec<(f64, f64)> },
}

#[derive(Clone)]
struct ColliderState {
    body_id: i64,
    shape: ColliderShape,
    sensor: bool,
    offset_x: f64,
    offset_y: f64,
    offset_rotation: f64,
}

struct PhysicsWorldState {
    gravity_x: f64,
    gravity_y: f64,
    next_body_id: i64,
    next_collider_id: i64,
    bodies: HashMap<i64, BodyState>,
    colliders: HashMap<i64, ColliderState>,
}

#[derive(Clone)]
struct ContactRecord {
    collider1: i64,
    collider2: i64,
    normal_x: f64,
    normal_y: f64,
    point_x: f64,
    point_y: f64,
    penetration: f64,
}

#[derive(Clone, Copy)]
struct Aabb {
    min_x: f64,
    max_x: f64,
    min_y: f64,
    max_y: f64,
}

fn get_i64(args: &[Value], index: usize, func: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "int")),
    }
}

fn get_f64(args: &[Value], index: usize, func: &str) -> Result<f64, CompileError> {
    match args.get(index) {
        Some(Value::Float(v)) => Ok(*v),
        Some(Value::Int(v)) => Ok(*v as f64),
        _ => Err(wrong_arg_type(func, index, "float")),
    }
}

fn get_bool(args: &[Value], index: usize, func: &str) -> Result<bool, CompileError> {
    match args.get(index) {
        Some(Value::Bool(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "bool")),
    }
}

fn get_f64_array(args: &[Value], index: usize, func: &str) -> Result<Vec<f64>, CompileError> {
    match args.get(index) {
        Some(Value::Array(values)) => {
            let mut out = Vec::with_capacity(values.len());
            for value in values.iter() {
                match value {
                    Value::Float(v) => out.push(*v),
                    Value::Int(v) => out.push(*v as f64),
                    _ => return Err(wrong_arg_type(func, index, "[f64]")),
                }
            }
            Ok(out)
        }
        _ => Err(wrong_arg_type(func, index, "[f64]")),
    }
}

fn world_body_aabb(body: &BodyState, collider: &ColliderState) -> Aabb {
    let center_x = body.x + collider.offset_x;
    let center_y = body.y + collider.offset_y;
    match &collider.shape {
        ColliderShape::Circle { radius } => Aabb {
            min_x: center_x - radius,
            max_x: center_x + radius,
            min_y: center_y - radius,
            max_y: center_y + radius,
        },
        ColliderShape::Box {
            half_width,
            half_height,
        } => Aabb {
            min_x: center_x - half_width,
            max_x: center_x + half_width,
            min_y: center_y - half_height,
            max_y: center_y + half_height,
        },
        ColliderShape::Capsule {
            half_height,
            radius,
        } => Aabb {
            min_x: center_x - radius,
            max_x: center_x + radius,
            min_y: center_y - half_height - radius,
            max_y: center_y + half_height + radius,
        },
        ColliderShape::Polygon { vertices } => {
            let mut min_x = center_x;
            let mut max_x = center_x;
            let mut min_y = center_y;
            let mut max_y = center_y;
            for (vx, vy) in vertices {
                min_x = min_x.min(center_x + vx);
                max_x = max_x.max(center_x + vx);
                min_y = min_y.min(center_y + vy);
                max_y = max_y.max(center_y + vy);
            }
            Aabb {
                min_x,
                max_x,
                min_y,
                max_y,
            }
        }
    }
}

fn aabb_overlap(a: Aabb, b: Aabb) -> Option<(f64, f64, f64, f64)> {
    let overlap_x = (a.max_x.min(b.max_x) - a.min_x.max(b.min_x)).max(0.0);
    let overlap_y = (a.max_y.min(b.max_y) - a.min_y.max(b.min_y)).max(0.0);
    if overlap_x > 0.0 && overlap_y > 0.0 {
        Some((overlap_x, overlap_y, (a.min_x + a.max_x) * 0.5, (a.min_y + a.max_y) * 0.5))
    } else {
        None
    }
}

fn compute_contacts(world: &PhysicsWorldState) -> Vec<ContactRecord> {
    let mut contacts = Vec::new();
    let collider_items: Vec<(i64, &ColliderState)> = world.colliders.iter().map(|(id, collider)| (*id, collider)).collect();
    for i in 0..collider_items.len() {
        for j in (i + 1)..collider_items.len() {
            let (id_a, collider_a) = collider_items[i];
            let (id_b, collider_b) = collider_items[j];
            let Some(body_a) = world.bodies.get(&collider_a.body_id) else {
                continue;
            };
            let Some(body_b) = world.bodies.get(&collider_b.body_id) else {
                continue;
            };
            let a = world_body_aabb(body_a, collider_a);
            let b = world_body_aabb(body_b, collider_b);
            if let Some((overlap_x, overlap_y, center_x, center_y)) = aabb_overlap(a, b) {
                let (normal_x, normal_y, penetration) = if overlap_x < overlap_y {
                    if center_x < (b.min_x + b.max_x) * 0.5 {
                        (-1.0, 0.0, overlap_x)
                    } else {
                        (1.0, 0.0, overlap_x)
                    }
                } else if center_y < (b.min_y + b.max_y) * 0.5 {
                    (0.0, -1.0, overlap_y)
                } else {
                    (0.0, 1.0, overlap_y)
                };
                contacts.push(ContactRecord {
                    collider1: id_a,
                    collider2: id_b,
                    normal_x,
                    normal_y,
                    point_x: center_x,
                    point_y: center_y,
                    penetration,
                });
            }
        }
    }
    contacts
}

fn resolve_dynamic_body(world: &mut PhysicsWorldState, body_id: i64, dt: f64) {
    let Some(body_snapshot) = world.bodies.get(&body_id).cloned() else {
        return;
    };
    if body_snapshot.body_type != 2 {
        return;
    }

    let body_colliders: Vec<(i64, ColliderState)> = world
        .colliders
        .iter()
        .filter(|(_, collider)| collider.body_id == body_id)
        .map(|(id, collider)| (*id, collider.clone()))
        .collect();
    let static_colliders: Vec<(i64, ColliderState, BodyState)> = world
        .colliders
        .iter()
        .filter(|(_, collider)| collider.body_id != body_id)
        .filter_map(|(id, collider)| {
            let other = world.bodies.get(&collider.body_id)?;
            Some((*id, collider.clone(), other.clone()))
        })
        .collect();

    let gravity_x = world.gravity_x;
    let gravity_y = -world.gravity_y;
    let Some(body) = world.bodies.get_mut(&body_id) else {
        return;
    };
    let inv_mass = if body_snapshot.mass.abs() < f64::EPSILON {
        1.0
    } else {
        1.0 / body_snapshot.mass
    };

    body.vx += (gravity_x + body.force_x * inv_mass) * dt;
    body.vy += (gravity_y + body.force_y * inv_mass) * dt;
    body.vx *= (1.0 - body.linear_damping * dt).max(0.0);
    body.vy *= (1.0 - body.linear_damping * dt).max(0.0);
    body.force_x = 0.0;
    body.force_y = 0.0;

    body.x += body.vx * dt;
    for (_, collider) in &body_colliders {
        let aabb = world_body_aabb(body, collider);
        for (_, other_collider, other_body) in &static_colliders {
            if other_body.body_type == 2 || collider.sensor || other_collider.sensor {
                continue;
            }
            let other_aabb = world_body_aabb(other_body, other_collider);
            if let Some((overlap_x, _, _, _)) = aabb_overlap(aabb, other_aabb) {
                if body.vx > 0.0 {
                    body.x -= overlap_x;
                } else if body.vx < 0.0 {
                    body.x += overlap_x;
                }
                body.vx = 0.0;
            }
        }
    }

    body.y += body.vy * dt;
    for (_, collider) in &body_colliders {
        let aabb = world_body_aabb(body, collider);
        for (_, other_collider, other_body) in &static_colliders {
            if other_body.body_type == 2 || collider.sensor || other_collider.sensor {
                continue;
            }
            let other_aabb = world_body_aabb(other_body, other_collider);
            if let Some((_, overlap_y, _, _)) = aabb_overlap(aabb, other_aabb) {
                if body.vy > 0.0 {
                    body.y -= overlap_y;
                } else if body.vy < 0.0 {
                    body.y += overlap_y;
                }
                body.vy = 0.0;
            }
        }
    }
}

pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_rapier2d_world_new" => {
            let gravity_x = get_f64(args, 0, name)?;
            let gravity_y = get_f64(args, 1, name)?;
            let world_id = NEXT_WORLD_ID.fetch_add(1, Ordering::SeqCst);
            WORLDS.lock().insert(
                world_id,
                PhysicsWorldState {
                    gravity_x,
                    gravity_y,
                    next_body_id: 1,
                    next_collider_id: 1,
                    bodies: HashMap::new(),
                    colliders: HashMap::new(),
                },
            );
            Ok(Value::Int(world_id))
        }
        "rt_rapier2d_world_free" => {
            let world_id = get_i64(args, 0, name)?;
            WORLDS.lock().remove(&world_id);
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_world_step" => {
            let world_id = get_i64(args, 0, name)?;
            let dt = get_f64(args, 1, name)?;
            let mut worlds = WORLDS.lock();
            if let Some(world) = worlds.get_mut(&world_id) {
                let body_ids: Vec<i64> = world.bodies.keys().copied().collect();
                for body_id in body_ids {
                    resolve_dynamic_body(world, body_id, dt);
                }
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_world_set_gravity" => {
            let world_id = get_i64(args, 0, name)?;
            let gravity_x = get_f64(args, 1, name)?;
            let gravity_y = get_f64(args, 2, name)?;
            if let Some(world) = WORLDS.lock().get_mut(&world_id) {
                world.gravity_x = gravity_x;
                world.gravity_y = gravity_y;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_new_dynamic" | "rt_rapier2d_body_new_static" | "rt_rapier2d_body_new_kinematic" => {
            let world_id = get_i64(args, 0, name)?;
            let x = get_f64(args, 1, name)?;
            let y = get_f64(args, 2, name)?;
            let rotation = get_f64(args, 3, name)?;
            let mut worlds = WORLDS.lock();
            let Some(world) = worlds.get_mut(&world_id) else {
                return Ok(Value::Int(0));
            };
            let body_id = world.next_body_id;
            world.next_body_id += 1;
            let body_type = if name.ends_with("dynamic") {
                2
            } else if name.ends_with("static") {
                0
            } else {
                1
            };
            world.bodies.insert(
                body_id,
                BodyState {
                    body_type,
                    x,
                    y,
                    rotation,
                    vx: 0.0,
                    vy: 0.0,
                    angular_velocity: 0.0,
                    force_x: 0.0,
                    force_y: 0.0,
                    mass: 1.0,
                    linear_damping: 0.0,
                    angular_damping: 0.0,
                    sleeping: false,
                },
            );
            Ok(Value::Int(body_id))
        }
        "rt_rapier2d_body_free" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            if let Some(world) = WORLDS.lock().get_mut(&world_id) {
                world.bodies.remove(&body_id);
                world.colliders.retain(|_, collider| collider.body_id != body_id);
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_get_position" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let worlds = WORLDS.lock();
            if let Some(world) = worlds.get(&world_id) {
                if let Some(body) = world.bodies.get(&body_id) {
                    return Ok(Value::Tuple(vec![
                        Value::Float(body.x),
                        Value::Float(body.y),
                        Value::Float(body.rotation),
                    ]));
                }
            }
            Ok(Value::Tuple(vec![Value::Float(0.0), Value::Float(0.0), Value::Float(0.0)]))
        }
        "rt_rapier2d_body_set_position" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let x = get_f64(args, 2, name)?;
            let y = get_f64(args, 3, name)?;
            let rotation = get_f64(args, 4, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.x = x;
                body.y = y;
                body.rotation = rotation;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_get_velocity" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let worlds = WORLDS.lock();
            if let Some(world) = worlds.get(&world_id) {
                if let Some(body) = world.bodies.get(&body_id) {
                    return Ok(Value::Tuple(vec![
                        Value::Float(body.vx),
                        Value::Float(body.vy),
                        Value::Float(body.angular_velocity),
                    ]));
                }
            }
            Ok(Value::Tuple(vec![Value::Float(0.0), Value::Float(0.0), Value::Float(0.0)]))
        }
        "rt_rapier2d_body_set_velocity" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let vx = get_f64(args, 2, name)?;
            let vy = get_f64(args, 3, name)?;
            let angular = get_f64(args, 4, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.vx = vx;
                body.vy = vy;
                body.angular_velocity = angular;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_apply_force" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let fx = get_f64(args, 2, name)?;
            let fy = get_f64(args, 3, name)?;
            let _wake_up = get_bool(args, 4, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.force_x += fx;
                body.force_y += fy;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_apply_impulse" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let ix = get_f64(args, 2, name)?;
            let iy = get_f64(args, 3, name)?;
            let _wake_up = get_bool(args, 4, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.vx += ix;
                body.vy += iy;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_apply_torque" | "rt_rapier2d_body_apply_torque_impulse" => Ok(Value::Bool(true)),
        "rt_rapier2d_body_set_mass" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let mass = get_f64(args, 2, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.mass = mass.max(0.001);
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_get_mass" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let worlds = WORLDS.lock();
            let mass = worlds
                .get(&world_id)
                .and_then(|world| world.bodies.get(&body_id))
                .map(|body| body.mass)
                .unwrap_or(0.0);
            Ok(Value::Float(mass))
        }
        "rt_rapier2d_body_set_linear_damping" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let damping = get_f64(args, 2, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.linear_damping = damping;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_set_angular_damping" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let damping = get_f64(args, 2, name)?;
            if let Some(body) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.bodies.get_mut(&body_id)) {
                body.angular_damping = damping;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_body_is_sleeping" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let sleeping = WORLDS
                .lock()
                .get(&world_id)
                .and_then(|world| world.bodies.get(&body_id))
                .map(|body| body.sleeping)
                .unwrap_or(false);
            Ok(Value::Bool(sleeping))
        }
        "rt_rapier2d_body_wake_up" => Ok(Value::Bool(true)),
        "rt_rapier2d_body_sleep" => Ok(Value::Bool(true)),
        "rt_rapier2d_collider_new_circle" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let radius = get_f64(args, 2, name)?;
            let mut worlds = WORLDS.lock();
            let Some(world) = worlds.get_mut(&world_id) else {
                return Ok(Value::Int(0));
            };
            let collider_id = world.next_collider_id;
            world.next_collider_id += 1;
            world.colliders.insert(
                collider_id,
                ColliderState {
                    body_id,
                    shape: ColliderShape::Circle { radius },
                    sensor: false,
                    offset_x: 0.0,
                    offset_y: 0.0,
                    offset_rotation: 0.0,
                },
            );
            Ok(Value::Int(collider_id))
        }
        "rt_rapier2d_collider_new_box" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let half_width = get_f64(args, 2, name)?;
            let half_height = get_f64(args, 3, name)?;
            let mut worlds = WORLDS.lock();
            let Some(world) = worlds.get_mut(&world_id) else {
                return Ok(Value::Int(0));
            };
            let collider_id = world.next_collider_id;
            world.next_collider_id += 1;
            world.colliders.insert(
                collider_id,
                ColliderState {
                    body_id,
                    shape: ColliderShape::Box {
                        half_width,
                        half_height,
                    },
                    sensor: false,
                    offset_x: 0.0,
                    offset_y: 0.0,
                    offset_rotation: 0.0,
                },
            );
            Ok(Value::Int(collider_id))
        }
        "rt_rapier2d_collider_new_capsule" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let half_height = get_f64(args, 2, name)?;
            let radius = get_f64(args, 3, name)?;
            let mut worlds = WORLDS.lock();
            let Some(world) = worlds.get_mut(&world_id) else {
                return Ok(Value::Int(0));
            };
            let collider_id = world.next_collider_id;
            world.next_collider_id += 1;
            world.colliders.insert(
                collider_id,
                ColliderState {
                    body_id,
                    shape: ColliderShape::Capsule { half_height, radius },
                    sensor: false,
                    offset_x: 0.0,
                    offset_y: 0.0,
                    offset_rotation: 0.0,
                },
            );
            Ok(Value::Int(collider_id))
        }
        "rt_rapier2d_collider_new_polygon" => {
            let world_id = get_i64(args, 0, name)?;
            let body_id = get_i64(args, 1, name)?;
            let raw_vertices = get_f64_array(args, 2, name)?;
            let mut vertices = Vec::new();
            let mut i = 0;
            while i + 1 < raw_vertices.len() {
                vertices.push((raw_vertices[i], raw_vertices[i + 1]));
                i += 2;
            }
            let mut worlds = WORLDS.lock();
            let Some(world) = worlds.get_mut(&world_id) else {
                return Ok(Value::Int(0));
            };
            let collider_id = world.next_collider_id;
            world.next_collider_id += 1;
            world.colliders.insert(
                collider_id,
                ColliderState {
                    body_id,
                    shape: ColliderShape::Polygon { vertices },
                    sensor: false,
                    offset_x: 0.0,
                    offset_y: 0.0,
                    offset_rotation: 0.0,
                },
            );
            Ok(Value::Int(collider_id))
        }
        "rt_rapier2d_collider_free" => {
            let world_id = get_i64(args, 0, name)?;
            let collider_id = get_i64(args, 1, name)?;
            if let Some(world) = WORLDS.lock().get_mut(&world_id) {
                world.colliders.remove(&collider_id);
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_collider_set_offset" => {
            let world_id = get_i64(args, 0, name)?;
            let collider_id = get_i64(args, 1, name)?;
            let offset_x = get_f64(args, 2, name)?;
            let offset_y = get_f64(args, 3, name)?;
            let offset_rotation = get_f64(args, 4, name)?;
            if let Some(collider) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.colliders.get_mut(&collider_id)) {
                collider.offset_x = offset_x;
                collider.offset_y = offset_y;
                collider.offset_rotation = offset_rotation;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_collider_set_restitution" | "rt_rapier2d_collider_set_friction" | "rt_rapier2d_collider_set_density" => {
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_collider_set_sensor" => {
            let world_id = get_i64(args, 0, name)?;
            let collider_id = get_i64(args, 1, name)?;
            let sensor = get_bool(args, 2, name)?;
            if let Some(collider) = WORLDS.lock().get_mut(&world_id).and_then(|world| world.colliders.get_mut(&collider_id)) {
                collider.sensor = sensor;
            }
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_world_get_contacts" => {
            let world_id = get_i64(args, 0, name)?;
            let worlds = WORLDS.lock();
            let contacts = worlds.get(&world_id).map(compute_contacts).unwrap_or_default();
            let list_id = NEXT_CONTACT_LIST_ID.fetch_add(1, Ordering::SeqCst);
            CONTACT_LISTS.lock().insert(list_id, contacts);
            Ok(Value::Int(list_id))
        }
        "rt_rapier2d_contacts_count" => {
            let list_id = get_i64(args, 0, name)?;
            let count = CONTACT_LISTS.lock().get(&list_id).map(|items| items.len() as i64).unwrap_or(0);
            Ok(Value::Int(count))
        }
        "rt_rapier2d_contacts_get" => {
            let list_id = get_i64(args, 0, name)?;
            let index = get_i64(args, 1, name)? as usize;
            let lists = CONTACT_LISTS.lock();
            if let Some(contact) = lists.get(&list_id).and_then(|items| items.get(index)) {
                return Ok(Value::Tuple(vec![
                    Value::Int(contact.collider1),
                    Value::Int(contact.collider2),
                    Value::Float(contact.normal_x),
                    Value::Float(contact.normal_y),
                    Value::Float(contact.point_x),
                    Value::Float(contact.point_y),
                    Value::Float(contact.penetration),
                ]));
            }
            Ok(Value::Tuple(vec![
                Value::Int(0),
                Value::Int(0),
                Value::Float(0.0),
                Value::Float(0.0),
                Value::Float(0.0),
                Value::Float(0.0),
                Value::Float(0.0),
            ]))
        }
        "rt_rapier2d_contacts_free" => {
            let list_id = get_i64(args, 0, name)?;
            CONTACT_LISTS.lock().remove(&list_id);
            Ok(Value::Bool(true))
        }
        "rt_rapier2d_world_intersection_test" => {
            let world_id = get_i64(args, 0, name)?;
            let collider1 = get_i64(args, 1, name)?;
            let collider2 = get_i64(args, 2, name)?;
            let worlds = WORLDS.lock();
            if let Some(world) = worlds.get(&world_id) {
                if let (Some(c1), Some(c2)) = (world.colliders.get(&collider1), world.colliders.get(&collider2)) {
                    if let (Some(b1), Some(b2)) = (world.bodies.get(&c1.body_id), world.bodies.get(&c2.body_id)) {
                        let overlaps = aabb_overlap(world_body_aabb(b1, c1), world_body_aabb(b2, c2)).is_some();
                        return Ok(Value::Bool(overlaps));
                    }
                }
            }
            Ok(Value::Bool(false))
        }
        "rt_rapier2d_world_cast_ray" => Ok(Value::Tuple(vec![Value::Bool(false), Value::Int(0), Value::Float(0.0)])),
        "rt_rapier2d_joint_distance"
        | "rt_rapier2d_joint_revolute"
        | "rt_rapier2d_joint_prismatic"
        | "rt_rapier2d_joint_fixed" => Ok(Value::Int(0)),
        "rt_rapier2d_joint_free" | "rt_rapier2d_joint_set_limits" | "rt_rapier2d_joint_set_motor" => Ok(Value::Bool(true)),
        "rt_rapier2d_world_body_count" => {
            let world_id = get_i64(args, 0, name)?;
            let count = WORLDS.lock().get(&world_id).map(|world| world.bodies.len() as i64).unwrap_or(0);
            Ok(Value::Int(count))
        }
        "rt_rapier2d_world_collider_count" => {
            let world_id = get_i64(args, 0, name)?;
            let count = WORLDS.lock().get(&world_id).map(|world| world.colliders.len() as i64).unwrap_or(0);
            Ok(Value::Int(count))
        }
        "rt_rapier2d_world_joint_count" => Ok(Value::Int(0)),
        "rt_rapier2d_get_last_error" => Ok(Value::Str(String::new())),
        _ => Err(unknown_function(name)),
    }
}
