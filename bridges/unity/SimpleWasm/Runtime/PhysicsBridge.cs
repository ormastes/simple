using UnityEngine;
using Wasmtime;

namespace SimpleWasm
{
    /// <summary>
    /// Implements the 12 engine_physics_* WASM ABI functions.
    /// All entity parameters are i32 handles resolved via HandleTable.
    /// </summary>
    public static class PhysicsBridge
    {
        /// <summary>
        /// Shared handle table — set by WasmBridge on init.
        /// </summary>
        public static HandleTable<GameObject> Entities { get; set; }

        /// <summary>
        /// engine_physics_add_rigidbody(entity: i32, body_type: i32)
        /// body_type: 0 = Dynamic, 1 = Kinematic, 2 = Static
        /// </summary>
        public static void AddRigidbody(int entity, int bodyType)
        {
            var go = Entities.Get(entity);
            if (go == null) return;

            var rb = go.GetComponent<Rigidbody>();
            if (rb == null)
                rb = go.AddComponent<Rigidbody>();

            switch (bodyType)
            {
                case 0: rb.isKinematic = false; break;
                case 1: rb.isKinematic = true;  break;
                case 2:
                    rb.isKinematic = true;
                    rb.useGravity = false;
                    break;
            }
        }

        /// <summary>
        /// engine_physics_set_mass(entity: i32, mass: f32)
        /// </summary>
        public static void SetMass(int entity, float mass)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var rb = go.GetComponent<Rigidbody>();
            if (rb != null) rb.mass = mass;
        }

        /// <summary>
        /// engine_physics_set_velocity(entity: i32, vx: f32, vy: f32, vz: f32)
        /// </summary>
        public static void SetVelocity(int entity, float vx, float vy, float vz)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var rb = go.GetComponent<Rigidbody>();
            if (rb != null) rb.velocity = new Vector3(vx, vy, vz);
        }

        /// <summary>
        /// engine_physics_get_velocity(entity: i32, out_ptr: i32)
        /// Writes 3 floats (vx, vy, vz) to WASM memory.
        /// </summary>
        public static void GetVelocity(Memory memory, int entity, int outPtr)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var rb = go.GetComponent<Rigidbody>();
            if (rb == null) return;

            Vector3 v = rb.velocity;
            memory.WriteFloat(outPtr, v.x);
            memory.WriteFloat(outPtr + 4, v.y);
            memory.WriteFloat(outPtr + 8, v.z);
        }

        /// <summary>
        /// engine_physics_add_force(entity: i32, fx: f32, fy: f32, fz: f32)
        /// </summary>
        public static void AddForce(int entity, float fx, float fy, float fz)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var rb = go.GetComponent<Rigidbody>();
            if (rb != null) rb.AddForce(new Vector3(fx, fy, fz), ForceMode.Force);
        }

        /// <summary>
        /// engine_physics_add_impulse(entity: i32, ix: f32, iy: f32, iz: f32)
        /// </summary>
        public static void AddImpulse(int entity, float ix, float iy, float iz)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var rb = go.GetComponent<Rigidbody>();
            if (rb != null) rb.AddForce(new Vector3(ix, iy, iz), ForceMode.Impulse);
        }

        /// <summary>
        /// engine_physics_add_collider_box(entity: i32, hx: f32, hy: f32, hz: f32)
        /// Half-extents for the box collider.
        /// </summary>
        public static void AddColliderBox(int entity, float hx, float hy, float hz)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var col = go.AddComponent<BoxCollider>();
            col.size = new Vector3(hx * 2f, hy * 2f, hz * 2f);
        }

        /// <summary>
        /// engine_physics_add_collider_sphere(entity: i32, radius: f32)
        /// </summary>
        public static void AddColliderSphere(int entity, float radius)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var col = go.AddComponent<SphereCollider>();
            col.radius = radius;
        }

        /// <summary>
        /// engine_physics_add_collider_capsule(entity: i32, radius: f32, height: f32)
        /// </summary>
        public static void AddColliderCapsule(int entity, float radius, float height)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var col = go.AddComponent<CapsuleCollider>();
            col.radius = radius;
            col.height = height;
        }

        /// <summary>
        /// engine_physics_raycast(ox, oy, oz, dx, dy, dz, max_dist, out_ptr) -> i32
        /// Returns 1 if hit, 0 if miss.
        /// On hit, writes 7 floats to out_ptr: hit_x, hit_y, hit_z, normal_x, normal_y, normal_z, distance
        /// </summary>
        public static int Raycast(Memory memory, float ox, float oy, float oz,
                                  float dx, float dy, float dz, float maxDist, int outPtr)
        {
            Vector3 origin = new Vector3(ox, oy, oz);
            Vector3 direction = new Vector3(dx, dy, dz).normalized;

            if (Physics.Raycast(origin, direction, out RaycastHit hit, maxDist))
            {
                memory.WriteFloat(outPtr, hit.point.x);
                memory.WriteFloat(outPtr + 4, hit.point.y);
                memory.WriteFloat(outPtr + 8, hit.point.z);
                memory.WriteFloat(outPtr + 12, hit.normal.x);
                memory.WriteFloat(outPtr + 16, hit.normal.y);
                memory.WriteFloat(outPtr + 20, hit.normal.z);
                memory.WriteFloat(outPtr + 24, hit.distance);
                return 1;
            }

            return 0;
        }

        /// <summary>
        /// engine_physics_set_gravity(gx: f32, gy: f32, gz: f32)
        /// </summary>
        public static void SetGravity(float gx, float gy, float gz)
        {
            Physics.gravity = new Vector3(gx, gy, gz);
        }

        /// <summary>
        /// engine_physics_set_collision_layer(entity: i32, layer: i32, mask: i32)
        /// </summary>
        public static void SetCollisionLayer(int entity, int layer, int mask)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            go.layer = layer;
            // Unity uses layer-based collision matrix; mask is informational here.
            // Full collision matrix control requires Physics.IgnoreLayerCollision calls.
        }
    }
}
