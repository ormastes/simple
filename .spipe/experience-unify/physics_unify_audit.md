# Physics Unify Audit — 2D/3D Shared Core (P2)
**Date:** 2026-06-12 | **Scope:** src/lib/nogc_sync_mut/engine/physics/ (read-only)

---

## 1. Current Shape — Dimension Classification

### 2D-Only
| File | Key assumption | Evidence |
|------|---------------|----------|
| `data/solver_body2d.spl` | `pos_x/y`, `vel_x/y`, `ang_vel: f64`, `rotation: f64` (scalar angle) | class SolverBodyStore2D fields |
| `data/constraint.spl` | `normal_x/y`, `point_x/y`, `lambda_n/t` (2-axis) | class ContactConstraintSoA |
| `broadphase/bvh2d.spl` | "Dynamic BVH Broad-Phase (2D)" — 2D AABB nodes | file header |
| `narrowphase/collision2d.spl` | circle/box 2D contacts, Vec2 normals | file header |
| `narrowphase/shapes2d.spl` | 2D shape descriptors (circle, box, capsule) | file name + import chain |
| `backend_cpu/simd_broadphase.spl` | 4-wide 2D AABB (min_x/y, max_x/y only) | "4-wide AABB overlap" header |
| `backend_cpu/scalar_solver.spl` | takes `SolverBodyStore2D` + `PhysicsConfig2D` | use imports |
| `backend_cpu/simd_solver.spl` | operates on 2D SoA bodies, 2-axis normals | file header |
| `backend_gpu/gpu_buffers.spl` | `body_pos_x/y`, `body_vel_x/y` — no z fields | struct GpuPhysicsBuffers |
| `backend_gpu/gpu_solver.spl` | drives GpuPhysicsBuffers (2D) | import chain |
| `world2d.spl` | `PhysicsWorld2D`, gravity Vec2, add_body by (x,y) | file header |
| `query/raycast2d.spl` | 2D ray origin+dir | file name |
| `graph/sleeping.spl` | `compute_kinetic_energy_2d(vx,vy,ang_vel,…)` | fn signature:line ~30 |
| `ccd.spl` | sweep in 2D (circle/box), CCDConfig no z | fn signatures |
| `character_controller.spl` | scalar gravity f64, no Vec3 | struct CharacterConfig |
| `joints.spl` | "2D Joint Types" — revolute/prismatic/weld 2D DOF | file header line 1 |
| `data/transform_buffer.spl` | 2D interpolation (prev/cur pos_x/y, rotation) | inferred from render_sync |

### 3D-Only
| File | Key assumption | Evidence |
|------|---------------|----------|
| `data/solver_body3d.spl` | `pos_x/y/z`, `vel_x/y/z`, `ang_vel_x/y/z`, quaternion `rot_w/x/y/z` | class SolverBodyStore3D fields |
| `narrowphase/collision3d.spl` | "3D Narrow-Phase" sphere-sphere, sphere-AABB, AABB-AABB | file header |
| `world3d.spl` | `PhysicsWorld3D`, gravity Vec3, quaternion rotation | file header + PhysicsConfig3D |

### Dimension-Agnostic Already
`collision_layers.spl` (i64 bitmask, no coords), `material.spl` (scalar f64), `backend.spl` (PhysicsBackend enum), `data/aosoa.spl` (layout helpers), `graph/island_manager.spl` (union-find on i64 indices), `graph/graph_coloring.spl` (ColorAssignment over constraint indices), `solver/tgs_solver.spl` (scalar TGS by index), `solver/xpbd_solver.spl` (gravity_x/y/z scalars), `integration/ecs_system.spl` (opaque world wrap), `integration/render_sync.spl` (2D now, pattern is generic), `ragdoll.spl` (bone i32 indices + scalar angles).

---

## 2. Duplication Map

| System | 2D location | 3D location | What's duplicated |
|--------|-------------|-------------|-------------------|
| SolverBody SoA | `solver_body2d.spl` | `solver_body3d.spl` | All fields except axis count; `inv_mass`, `inv_inertia*`, `linear_damping`, `angular_damping`, `gravity_scale`, `body_type` identical |
| Config struct | `config.spl::PhysicsConfig2D` | `config.spl::PhysicsConfig3D` | All scalar fields identical (fixed_timestep, sub_steps, iterations, sleep, baumgarte, slop, backend); gravity type differs (Vec2 vs Vec3) |
| World top-level | `world2d.spl` (378 ln) | `world3d.spl` (307 ln) | Backend dispatch loop, body-index management, add_static/dynamic_body pattern, step() orchestration |
| Narrowphase dispatch | `collision2d.spl` | `collision3d.spl` | Contact struct shape identical; GJK/EPA fully separate; ~80% boilerplate contact output identical |
| Sleeping | `sleeping.spl::compute_kinetic_energy_2d` | none (3D world repeats inline) | KE formula; sleep-timer loop |
| Broadphase | `bvh2d.spl` | none (3D uses bvh2d with AABB extension hack?) | BVH tree structure; pair emission |
| Pair manager | `pair_manager.spl` | none | Add/remove pair diffing; works on i64 collider IDs — already dimension-free in logic, just named "Physics2" |
| Contact cache | `contact_cache.spl` | none (3D re-builds per step) | Warm-start accumulation via feature_id_a/b; currently 2D only |
| GPU buffers | `gpu_buffers.spl` | none | GPU path is 2D-only; 3D has no GPU acceleration yet |

---

## 3. Shared-Core Seams — Ordered Refactor Steps

**Step S1 — Extract `PhysicsConfigCommon`** (½ day, risk: LOW, prereq: none)
Move all scalar fields shared between `PhysicsConfig2D` and `PhysicsConfig3D` into a `PhysicsConfigCommon` struct. Both config types embed it. No logic change.

**Step S2 — Unify `CollisionFilter` + `CollisionLayerTable`** (already done — confirm & re-export, ½ day, risk: NONE)
`collision_layers.spl` is already dimension-free. Add a single `export` from a new `physics_core` namespace so both world2d and world3d import from one place rather than duplicating the `use` path.

**Step S3 — Extract `SolverBodyCore` fields** (1 day, risk: LOW, prereq: none)
Create `data/solver_body_core.spl` with the shared scalar arrays (`inv_mass`, `inv_inertia*`, `linear_damping`, `angular_damping`, `gravity_scale`, `body_type`, `node_ids`, `body_count`). `SolverBodyStore2D` and `SolverBodyStore3D` embed it via composition. Existing field-access sites update to `store.core.inv_mass[i]`.

**Step S4 — Unify `compute_kinetic_energy`** (½ day, risk: LOW, prereq: S3)
Move `compute_kinetic_energy_2d` to `graph/sleeping.spl` plus add `compute_kinetic_energy_3d`. Both called from a shared `update_sleeping_generic` that takes only the shared scalar fields from S3.

**Step S5 — Dimension-free `PairManager`** (½ day, risk: LOW, prereq: none)
`pair_manager.spl` is already logically dimension-free (operates on i64 IDs). Remove the `# Physics2` namespace comment, rename to `broadphase/pair_manager.spl` under a generic namespace, and confirm world3d imports it.

**Step S6 — Shared `ContactConstraintSoA` + contact cache** (1 day, risk: MEDIUM, prereq: none)
`ContactConstraintSoA` currently has `normal_x/y` and `point_x/y`. Add `normal_z: [f64]` and `point_z: [f64]` as optional-zero 3D extension. Alternatively extract a generic struct with a `DIM` count. Warm-start cache (`contact_cache.spl`) then works for both worlds; world3d gains warm-starting.

**Step S7 — `tgs_solver` made dimension-aware** (1 day, risk: MEDIUM, prereq: S6)
`tgs_solver` currently reads only `normal_x/y` for the Jacobian. Parameterize the relative-velocity calculation to optionally include z. Scalar reference stays unchanged; SIMD path gets a flag or separate fn.

**Step S8 — Shared `IslandManager` + `GraphColoring` by value** (already dimension-free, ½ day, risk: LOW, prereq: S4)
Confirm world3d instantiates `IslandManager` and `ColorAssignment` from the same files. If not, wire them in.

**Step S9 — `render_sync` generic over 2D/3D** (1 day, risk: LOW, prereq: S3)
`render_sync.spl` currently produces `TransformBuffer2D`. Add `TransformBuffer3D` variant or make it generic over position type. ECS system stays a thin adapter above each.

**Step S10 — BVH for 3D** (1 day, risk: MEDIUM, prereq: S5)
Add `broadphase/bvh3d.spl` by copying `bvh2d.spl` and extending node AABB to min_z/max_z. Do NOT try to generic-parameterize bvh2d — 2D SIMD 4-wide test becomes fragile.

---

## 4. What NOT to Unify

| Item | Reason |
|------|--------|
| **Joint types** | 2D = scalar angle + 1 DOF; 3D = quaternion + 6 DOF — different Jacobians entirely |
| **Gravity field** | Vec2 vs Vec3; forcing Vec3 in 2D creates silent z=0 bugs in gravity-scale math |
| **Rotation** | 2D scalar f64 angle vs 3D quaternion — incompatible without a union type |
| **Narrowphase shapes** | circle/box vs sphere/OBB — different GJK maps; share contact output (S6), not detection |
| **CCD kernels** | 2D bisection ~50 lines; 3D TOI needs GJK sweep — different algorithm family |
| **CharacterController** | 2D slope/grounded logic ≠ 3D; share only scalar config fields |
| **GPU buffers** | 3D needs ~10 SoA arrays vs 2D 7; couple separately to avoid stride mismatch |
| **Cloth/destruction** | Cloth via XpbdWorld (already dim-bridged); destruction is 2D voronoi only |

---

## 5. Determinism + SIMD Notes

| Location | Issue |
|----------|-------|
| `backend_cpu/simd_solver.spl` | "In interpreter mode, this runs as scalar loops" — SIMD path non-deterministic across lane orderings; a `#[deterministic]` flag must disable the SIMD batch grouping and fall back to scalar_solver |
| `backend_cpu/simd_broadphase.spl` | 4-wide AABB test produces bitmask — order of pair emission depends on which 4 children happen to be grouped; determinism flag must enforce sorted pair ordering |
| `graph/graph_coloring.spl` | Color assignment is graph-topology-deterministic but not insertion-order-deterministic if bodies are added concurrently; guard: single-threaded island build under determinism flag |
| `backend_gpu/gpu_solver.spl` | GPU atomic accumulation is non-deterministic by definition; determinism flag must exclude `PhysicsBackend.Gpu` |
| `solver/xpbd_solver.spl` | `gravity_x/y/z` stored as separate f64 — safe for determinism; no SIMD paths |
| `data/solver_body2d/3d` | All f64 SoA; deterministic if loop order is fixed — no hazard in scalar mode |
| **Global rule** | Rapier model: `determinism` compile flag → disable SIMD + parallel island solve + GPU backend; scalar TGS only. Add `PhysicsBackend.CpuScalarDeterministic` variant rather than a global flag to keep backend selection explicit |
