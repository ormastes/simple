using UnityEngine;
using Wasmtime;

namespace SimpleWasm
{
    /// <summary>
    /// Implements the 14 engine_render_* WASM ABI functions.
    /// Creates GameObjects with mesh renderers, lights, and cameras.
    /// </summary>
    public static class RenderBridge
    {
        /// <summary>
        /// Shared entity handle table. Set by WasmBridge on init.
        /// </summary>
        public static HandleTable<GameObject> Entities { get; set; }

        /// <summary>
        /// Material handle table. Set by WasmBridge on init.
        /// </summary>
        public static HandleTable<Material> Materials { get; set; }

        /// <summary>
        /// Asset handle table for textures. Set by WasmBridge on init.
        /// </summary>
        public static HandleTable<Object> Assets { get; set; }

        /// <summary>
        /// Mesh type constants matching Simple Game3D enum.
        /// </summary>
        private enum MeshType
        {
            Cube = 0,
            Sphere = 1,
            Capsule = 2,
            Cylinder = 3,
            Plane = 4,
            Quad = 5
        }

        /// <summary>
        /// Light type constants matching Simple Game3D enum.
        /// </summary>
        private enum SimpleLightType
        {
            Directional = 0,
            Point = 1,
            Spot = 2
        }

        /// <summary>
        /// engine_render_set_mesh(entity: i32, mesh_type: i32)
        /// Sets a built-in primitive mesh on the entity.
        /// </summary>
        public static void SetMesh(int entity, int meshType)
        {
            var go = Entities.Get(entity);
            if (go == null) return;

            var filter = go.GetComponent<MeshFilter>();
            if (filter == null)
                filter = go.AddComponent<MeshFilter>();

            var renderer = go.GetComponent<MeshRenderer>();
            if (renderer == null)
            {
                renderer = go.AddComponent<MeshRenderer>();
                renderer.material = new Material(Shader.Find("Standard"));
            }

            filter.mesh = GetPrimitiveMesh((MeshType)meshType);
        }

        /// <summary>
        /// engine_render_set_mesh_asset(entity: i32, asset_id: i32)
        /// Sets a mesh loaded via asset system on the entity.
        /// </summary>
        public static void SetMeshAsset(int entity, int assetId)
        {
            var go = Entities.Get(entity);
            if (go == null) return;

            var meshObj = Assets.Get(assetId) as Mesh;
            if (meshObj == null) return;

            var filter = go.GetComponent<MeshFilter>();
            if (filter == null)
                filter = go.AddComponent<MeshFilter>();

            var renderer = go.GetComponent<MeshRenderer>();
            if (renderer == null)
            {
                renderer = go.AddComponent<MeshRenderer>();
                renderer.material = new Material(Shader.Find("Standard"));
            }

            filter.mesh = meshObj;
        }

        /// <summary>
        /// engine_render_set_material(entity: i32, material_id: i32)
        /// </summary>
        public static void SetMaterial(int entity, int materialId)
        {
            var go = Entities.Get(entity);
            if (go == null) return;
            var mat = Materials.Get(materialId);
            if (mat == null) return;

            var renderer = go.GetComponent<MeshRenderer>();
            if (renderer != null) renderer.material = mat;
        }

        /// <summary>
        /// engine_render_create_material() -> i32
        /// </summary>
        public static int CreateMaterial()
        {
            var mat = new Material(Shader.Find("Standard"));
            return Materials.Add(mat);
        }

        /// <summary>
        /// engine_render_set_material_color(material: i32, r: f32, g: f32, b: f32, a: f32)
        /// </summary>
        public static void SetMaterialColor(int materialId, float r, float g, float b, float a)
        {
            var mat = Materials.Get(materialId);
            if (mat != null) mat.color = new Color(r, g, b, a);
        }

        /// <summary>
        /// engine_render_set_material_texture(material: i32, slot: i32, texture_id: i32)
        /// slot: 0 = _MainTex, 1 = _BumpMap, 2 = _MetallicGlossMap, 3 = _OcclusionMap
        /// </summary>
        public static void SetMaterialTexture(int materialId, int slot, int textureId)
        {
            var mat = Materials.Get(materialId);
            if (mat == null) return;

            var tex = Assets.Get(textureId) as Texture;
            if (tex == null) return;

            string propName;
            switch (slot)
            {
                case 0:  propName = "_MainTex"; break;
                case 1:  propName = "_BumpMap"; break;
                case 2:  propName = "_MetallicGlossMap"; break;
                case 3:  propName = "_OcclusionMap"; break;
                default: propName = "_MainTex"; break;
            }

            mat.SetTexture(propName, tex);
        }

        /// <summary>
        /// engine_render_set_material_float(material: i32, param: i32, value: f32)
        /// param: 0 = _Metallic, 1 = _Glossiness, 2 = _BumpScale
        /// </summary>
        public static void SetMaterialFloat(int materialId, int param, float value)
        {
            var mat = Materials.Get(materialId);
            if (mat == null) return;

            string propName;
            switch (param)
            {
                case 0:  propName = "_Metallic"; break;
                case 1:  propName = "_Glossiness"; break;
                case 2:  propName = "_BumpScale"; break;
                default: propName = "_Metallic"; break;
            }

            mat.SetFloat(propName, value);
        }

        /// <summary>
        /// engine_render_create_light(light_type: i32) -> i32
        /// Returns entity handle for the light's GameObject.
        /// </summary>
        public static int CreateLight(int lightType)
        {
            var go = new GameObject("SimpleWasm_Light");
            var light = go.AddComponent<Light>();

            switch ((SimpleLightType)lightType)
            {
                case SimpleLightType.Directional:
                    light.type = LightType.Directional;
                    break;
                case SimpleLightType.Point:
                    light.type = LightType.Point;
                    break;
                case SimpleLightType.Spot:
                    light.type = LightType.Spot;
                    break;
            }

            return Entities.Add(go);
        }

        /// <summary>
        /// engine_render_set_light_color(light: i32, r: f32, g: f32, b: f32)
        /// </summary>
        public static void SetLightColor(int lightHandle, float r, float g, float b)
        {
            var go = Entities.Get(lightHandle);
            if (go == null) return;
            var light = go.GetComponent<Light>();
            if (light != null) light.color = new Color(r, g, b);
        }

        /// <summary>
        /// engine_render_set_light_intensity(light: i32, intensity: f32)
        /// </summary>
        public static void SetLightIntensity(int lightHandle, float intensity)
        {
            var go = Entities.Get(lightHandle);
            if (go == null) return;
            var light = go.GetComponent<Light>();
            if (light != null) light.intensity = intensity;
        }

        /// <summary>
        /// engine_render_create_camera() -> i32
        /// Returns entity handle for the camera's GameObject.
        /// </summary>
        public static int CreateCamera()
        {
            var go = new GameObject("SimpleWasm_Camera");
            go.AddComponent<Camera>();
            go.AddComponent<AudioListener>();
            return Entities.Add(go);
        }

        /// <summary>
        /// engine_render_set_camera_fov(camera: i32, fov: f32)
        /// </summary>
        public static void SetCameraFov(int cameraHandle, float fov)
        {
            var go = Entities.Get(cameraHandle);
            if (go == null) return;
            var cam = go.GetComponent<Camera>();
            if (cam != null) cam.fieldOfView = fov;
        }

        /// <summary>
        /// engine_render_set_camera_active(camera: i32, active: i32)
        /// </summary>
        public static void SetCameraActive(int cameraHandle, int active)
        {
            var go = Entities.Get(cameraHandle);
            if (go == null) return;
            var cam = go.GetComponent<Camera>();
            if (cam != null) cam.enabled = active != 0;
        }

        /// <summary>
        /// engine_render_create_primitive(prim_type: i32) -> i32
        /// Creates a new entity with a primitive mesh and default material.
        /// </summary>
        public static int CreatePrimitive(int primType)
        {
            PrimitiveType unityPrim;
            switch ((MeshType)primType)
            {
                case MeshType.Cube:     unityPrim = PrimitiveType.Cube; break;
                case MeshType.Sphere:   unityPrim = PrimitiveType.Sphere; break;
                case MeshType.Capsule:  unityPrim = PrimitiveType.Capsule; break;
                case MeshType.Cylinder: unityPrim = PrimitiveType.Cylinder; break;
                case MeshType.Plane:    unityPrim = PrimitiveType.Plane; break;
                case MeshType.Quad:     unityPrim = PrimitiveType.Quad; break;
                default:                unityPrim = PrimitiveType.Cube; break;
            }

            var go = GameObject.CreatePrimitive(unityPrim);
            go.name = $"SimpleWasm_Primitive_{unityPrim}";
            return Entities.Add(go);
        }

        /// <summary>
        /// Get a built-in Unity primitive mesh by type.
        /// </summary>
        private static Mesh GetPrimitiveMesh(MeshType type)
        {
            PrimitiveType unityPrim;
            switch (type)
            {
                case MeshType.Cube:     unityPrim = PrimitiveType.Cube; break;
                case MeshType.Sphere:   unityPrim = PrimitiveType.Sphere; break;
                case MeshType.Capsule:  unityPrim = PrimitiveType.Capsule; break;
                case MeshType.Cylinder: unityPrim = PrimitiveType.Cylinder; break;
                case MeshType.Plane:    unityPrim = PrimitiveType.Plane; break;
                case MeshType.Quad:     unityPrim = PrimitiveType.Quad; break;
                default:                unityPrim = PrimitiveType.Cube; break;
            }

            // Create a temporary primitive to extract its mesh, then destroy the GO
            var tempGo = GameObject.CreatePrimitive(unityPrim);
            var mesh = tempGo.GetComponent<MeshFilter>().sharedMesh;
            Object.DestroyImmediate(tempGo);
            return mesh;
        }
    }
}
