using System;
using System.IO;
using System.Text;
using UnityEngine;
using Wasmtime;

namespace SimpleWasm
{
    /// <summary>
    /// Core bridge MonoBehaviour that loads a Simple-compiled .wasm module
    /// and provides all 68 engine_* functions as WASM imports.
    ///
    /// Attach to a GameObject and set wasmPath to the .wasm file location.
    /// The bridge calls game_init on Start, game_update each frame, and
    /// game_shutdown on destroy.
    ///
    /// Supports hot-reload: watches the .wasm file timestamp and reloads
    /// automatically when the file changes.
    /// </summary>
    public class WasmBridge : MonoBehaviour
    {
        [SerializeField]
        [Tooltip("Path to the .wasm module file")]
        private string wasmPath = "";

        // Wasmtime runtime objects
        private Engine _engine;
        private Store _store;
        private Linker _linker;
        private Instance _instance;
        private Memory _memory;

        // WASM exports
        private Action _gameInit;
        private Action _gameUpdate;
        private Action _gameShutdown;

        // Handle tables
        private HandleTable<GameObject> _entities;
        private HandleTable<Material> _materials;
        private HandleTable<UnityEngine.Object> _assets;
        private HandleTable<AudioSource> _audioSources;

        // Hot-reload state
        private DateTime _lastWriteTime;
        private bool _loaded;

        // Audio root
        private Transform _audioRoot;

        /// <summary>Whether the WASM module is currently loaded.</summary>
        public bool IsLoaded => _loaded;

        /// <summary>Number of live entity handles.</summary>
        public int EntityCount => _entities?.Count ?? 0;

        // =====================================================================
        // Unity Lifecycle
        // =====================================================================

        private void Start()
        {
            InitHandleTables();
            LoadWasm();
        }

        private void Update()
        {
            if (!_loaded) return;

            // Hot-reload: check file timestamp
            CheckHotReload();

            // Call game_update export
            try
            {
                _gameUpdate?.Invoke();
            }
            catch (Exception e)
            {
                Debug.LogError($"[SimpleWasm] game_update error: {e.Message}");
            }
        }

        private void OnDestroy()
        {
            ShutdownWasm();
        }

        // =====================================================================
        // Public API
        // =====================================================================

        /// <summary>
        /// Force reload the WASM module. Called from inspector or scripts.
        /// </summary>
        public void ReloadWasm()
        {
            ShutdownWasm();
            InitHandleTables();
            LoadWasm();
        }

        // =====================================================================
        // WASM Loading
        // =====================================================================

        private void InitHandleTables()
        {
            _entities = new HandleTable<GameObject>();
            _materials = new HandleTable<Material>();
            _assets = new HandleTable<UnityEngine.Object>();
            _audioSources = new HandleTable<AudioSource>();

            // Share tables with bridge classes
            PhysicsBridge.Entities = _entities;
            RenderBridge.Entities = _entities;
            RenderBridge.Materials = _materials;
            RenderBridge.Assets = _assets;
            AudioBridge.Sources = _audioSources;
            AudioBridge.Entities = _entities;

            // Create audio root
            if (_audioRoot == null)
            {
                var audioGo = new GameObject("SimpleWasm_AudioRoot");
                audioGo.transform.SetParent(transform);
                _audioRoot = audioGo.transform;
            }
            AudioBridge.AudioRoot = _audioRoot;
        }

        private void LoadWasm()
        {
            if (string.IsNullOrEmpty(wasmPath))
            {
                Debug.LogWarning("[SimpleWasm] No WASM path specified.");
                return;
            }

            if (!File.Exists(wasmPath))
            {
                Debug.LogError($"[SimpleWasm] WASM file not found: {wasmPath}");
                return;
            }

            try
            {
                _engine = new Engine();
                _store = new Store(_engine);
                _linker = new Linker(_engine);

                RegisterAllImports();

                var module = Module.FromFile(_engine, wasmPath);
                _instance = _linker.Instantiate(_store, module);

                // Get linear memory
                _memory = _instance.GetMemory("memory");
                if (_memory == null)
                    Debug.LogWarning("[SimpleWasm] WASM module has no 'memory' export.");

                // Get game lifecycle exports
                _gameInit = _instance.GetAction("game_init");
                _gameUpdate = _instance.GetAction("game_update");
                _gameShutdown = _instance.GetAction("game_shutdown");

                _lastWriteTime = File.GetLastWriteTimeUtc(wasmPath);
                _loaded = true;

                Debug.Log($"[SimpleWasm] Loaded: {wasmPath}");

                // Call game_init
                _gameInit?.Invoke();
            }
            catch (Exception e)
            {
                Debug.LogError($"[SimpleWasm] Failed to load WASM: {e.Message}\n{e.StackTrace}");
                _loaded = false;
            }
        }

        private void ShutdownWasm()
        {
            if (_loaded)
            {
                try
                {
                    _gameShutdown?.Invoke();
                }
                catch (Exception e)
                {
                    Debug.LogWarning($"[SimpleWasm] game_shutdown error: {e.Message}");
                }
            }

            // Clean up entities
            if (_entities != null)
            {
                _entities.Clear();
            }
            if (_materials != null) _materials.Clear();
            if (_assets != null) _assets.Clear();
            if (_audioSources != null) _audioSources.Clear();

            _instance = null;
            _memory = null;
            _gameInit = null;
            _gameUpdate = null;
            _gameShutdown = null;

            _store?.Dispose();
            _store = null;
            _linker = null;
            _engine?.Dispose();
            _engine = null;

            _loaded = false;
        }

        private void CheckHotReload()
        {
            if (string.IsNullOrEmpty(wasmPath) || !File.Exists(wasmPath))
                return;

            var currentTime = File.GetLastWriteTimeUtc(wasmPath);
            if (currentTime > _lastWriteTime)
            {
                Debug.Log("[SimpleWasm] WASM file changed, hot-reloading...");
                ReloadWasm();
            }
        }

        // =====================================================================
        // Memory Helpers
        // =====================================================================

        private string ReadString(int ptr, int len)
        {
            if (_memory == null || len <= 0) return "";
            return _memory.ReadString(ptr, len);
        }

        private void WriteFloat(int ptr, float value)
        {
            _memory?.WriteFloat(ptr, value);
        }

        private float ReadFloat(int ptr)
        {
            return _memory?.ReadFloat(ptr) ?? 0f;
        }

        // =====================================================================
        // Import Registration — all 68 engine_* functions
        // =====================================================================

        private void RegisterAllImports()
        {
            RegisterEntityImports();
            RegisterTransformImports();
            RegisterRenderImports();
            RegisterInputImports();
            RegisterPhysicsImports();
            RegisterAudioImports();
            RegisterAssetImports();
            RegisterDebugImports();
        }

        // -----------------------------------------------------------------
        // Entity Management (8 functions)
        // -----------------------------------------------------------------
        private void RegisterEntityImports()
        {
            _linker.DefineFunction("engine", "engine_entity_create",
                () =>
                {
                    var go = new GameObject("SimpleWasm_Entity");
                    return _entities.Add(go);
                });

            _linker.DefineFunction("engine", "engine_entity_create_named",
                (int namePtr, int nameLen) =>
                {
                    string name = ReadString(namePtr, nameLen);
                    var go = new GameObject(name);
                    return _entities.Add(go);
                });

            _linker.DefineFunction("engine", "engine_entity_destroy",
                (int entity) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null)
                    {
                        UnityEngine.Object.Destroy(go);
                        _entities.Remove(entity);
                    }
                });

            _linker.DefineFunction("engine", "engine_entity_set_active",
                (int entity, int active) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.SetActive(active != 0);
                });

            _linker.DefineFunction("engine", "engine_entity_is_active",
                (int entity) =>
                {
                    var go = _entities.Get(entity);
                    return (go != null && go.activeSelf) ? 1 : 0;
                });

            _linker.DefineFunction("engine", "engine_entity_set_parent",
                (int entity, int parent) =>
                {
                    var child = _entities.Get(entity);
                    var parentGo = _entities.Get(parent);
                    if (child != null && parentGo != null)
                        child.transform.SetParent(parentGo.transform);
                });

            _linker.DefineFunction("engine", "engine_entity_set_name",
                (int entity, int namePtr, int nameLen) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.name = ReadString(namePtr, nameLen);
                });

            _linker.DefineFunction("engine", "engine_entity_find_by_name",
                (int namePtr, int nameLen) =>
                {
                    string name = ReadString(namePtr, nameLen);
                    var go = GameObject.Find(name);
                    if (go == null) return -1;
                    return _entities.Add(go);
                });
        }

        // -----------------------------------------------------------------
        // Transform (12 functions)
        // -----------------------------------------------------------------
        private void RegisterTransformImports()
        {
            _linker.DefineFunction("engine", "engine_transform_get_position",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Vector3 p = go.transform.position;
                    WriteFloat(outPtr, p.x);
                    WriteFloat(outPtr + 4, p.y);
                    WriteFloat(outPtr + 8, p.z);
                });

            _linker.DefineFunction("engine", "engine_transform_set_position",
                (int entity, float x, float y, float z) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.transform.position = new Vector3(x, y, z);
                });

            _linker.DefineFunction("engine", "engine_transform_get_rotation",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Quaternion q = go.transform.rotation;
                    // Write as x, y, z, w to match Simple's Quat layout
                    WriteFloat(outPtr, q.x);
                    WriteFloat(outPtr + 4, q.y);
                    WriteFloat(outPtr + 8, q.z);
                    WriteFloat(outPtr + 12, q.w);
                });

            _linker.DefineFunction("engine", "engine_transform_set_rotation",
                (int entity, float x, float y, float z, float w) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null)
                        go.transform.rotation = new Quaternion(x, y, z, w);
                });

            _linker.DefineFunction("engine", "engine_transform_get_scale",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Vector3 s = go.transform.localScale;
                    WriteFloat(outPtr, s.x);
                    WriteFloat(outPtr + 4, s.y);
                    WriteFloat(outPtr + 8, s.z);
                });

            _linker.DefineFunction("engine", "engine_transform_set_scale",
                (int entity, float x, float y, float z) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.transform.localScale = new Vector3(x, y, z);
                });

            _linker.DefineFunction("engine", "engine_transform_look_at",
                (int entity, float x, float y, float z) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.transform.LookAt(new Vector3(x, y, z));
                });

            _linker.DefineFunction("engine", "engine_transform_translate",
                (int entity, float dx, float dy, float dz) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null) go.transform.Translate(dx, dy, dz);
                });

            _linker.DefineFunction("engine", "engine_transform_rotate",
                (int entity, float axisX, float axisY, float axisZ, float angle) =>
                {
                    var go = _entities.Get(entity);
                    if (go != null)
                        go.transform.Rotate(new Vector3(axisX, axisY, axisZ), angle);
                });

            _linker.DefineFunction("engine", "engine_transform_get_forward",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Vector3 f = go.transform.forward;
                    WriteFloat(outPtr, f.x);
                    WriteFloat(outPtr + 4, f.y);
                    WriteFloat(outPtr + 8, f.z);
                });

            _linker.DefineFunction("engine", "engine_transform_get_up",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Vector3 u = go.transform.up;
                    WriteFloat(outPtr, u.x);
                    WriteFloat(outPtr + 4, u.y);
                    WriteFloat(outPtr + 8, u.z);
                });

            _linker.DefineFunction("engine", "engine_transform_get_right",
                (int entity, int outPtr) =>
                {
                    var go = _entities.Get(entity);
                    if (go == null) return;
                    Vector3 r = go.transform.right;
                    WriteFloat(outPtr, r.x);
                    WriteFloat(outPtr + 4, r.y);
                    WriteFloat(outPtr + 8, r.z);
                });
        }

        // -----------------------------------------------------------------
        // Rendering (14 functions)
        // -----------------------------------------------------------------
        private void RegisterRenderImports()
        {
            _linker.DefineFunction("engine", "engine_render_set_mesh",
                (int entity, int meshType) =>
                {
                    RenderBridge.SetMesh(entity, meshType);
                });

            _linker.DefineFunction("engine", "engine_render_set_mesh_asset",
                (int entity, int assetId) =>
                {
                    RenderBridge.SetMeshAsset(entity, assetId);
                });

            _linker.DefineFunction("engine", "engine_render_set_material",
                (int entity, int materialId) =>
                {
                    RenderBridge.SetMaterial(entity, materialId);
                });

            _linker.DefineFunction("engine", "engine_render_create_material",
                () =>
                {
                    return RenderBridge.CreateMaterial();
                });

            _linker.DefineFunction("engine", "engine_render_set_material_color",
                (int material, float r, float g, float b, float a) =>
                {
                    RenderBridge.SetMaterialColor(material, r, g, b, a);
                });

            _linker.DefineFunction("engine", "engine_render_set_material_texture",
                (int material, int slot, int textureId) =>
                {
                    RenderBridge.SetMaterialTexture(material, slot, textureId);
                });

            _linker.DefineFunction("engine", "engine_render_set_material_float",
                (int material, int param, float value) =>
                {
                    RenderBridge.SetMaterialFloat(material, param, value);
                });

            _linker.DefineFunction("engine", "engine_render_create_light",
                (int lightType) =>
                {
                    return RenderBridge.CreateLight(lightType);
                });

            _linker.DefineFunction("engine", "engine_render_set_light_color",
                (int light, float r, float g, float b) =>
                {
                    RenderBridge.SetLightColor(light, r, g, b);
                });

            _linker.DefineFunction("engine", "engine_render_set_light_intensity",
                (int light, float intensity) =>
                {
                    RenderBridge.SetLightIntensity(light, intensity);
                });

            _linker.DefineFunction("engine", "engine_render_create_camera",
                () =>
                {
                    return RenderBridge.CreateCamera();
                });

            _linker.DefineFunction("engine", "engine_render_set_camera_fov",
                (int camera, float fov) =>
                {
                    RenderBridge.SetCameraFov(camera, fov);
                });

            _linker.DefineFunction("engine", "engine_render_set_camera_active",
                (int camera, int active) =>
                {
                    RenderBridge.SetCameraActive(camera, active);
                });

            _linker.DefineFunction("engine", "engine_render_create_primitive",
                (int primType) =>
                {
                    return RenderBridge.CreatePrimitive(primType);
                });
        }

        // -----------------------------------------------------------------
        // Input (8 functions)
        // -----------------------------------------------------------------
        private void RegisterInputImports()
        {
            _linker.DefineFunction("engine", "engine_input_is_key_pressed",
                (int keyCode) =>
                {
                    return InputBridge.IsKeyPressed(keyCode);
                });

            _linker.DefineFunction("engine", "engine_input_is_key_just_pressed",
                (int keyCode) =>
                {
                    return InputBridge.IsKeyJustPressed(keyCode);
                });

            _linker.DefineFunction("engine", "engine_input_is_key_just_released",
                (int keyCode) =>
                {
                    return InputBridge.IsKeyJustReleased(keyCode);
                });

            _linker.DefineFunction("engine", "engine_input_get_mouse_position",
                (int outPtr) =>
                {
                    InputBridge.GetMousePosition(_memory, outPtr);
                });

            _linker.DefineFunction("engine", "engine_input_get_mouse_delta",
                (int outPtr) =>
                {
                    InputBridge.GetMouseDelta(_memory, outPtr);
                });

            _linker.DefineFunction("engine", "engine_input_is_mouse_button_pressed",
                (int button) =>
                {
                    return InputBridge.IsMouseButtonPressed(button);
                });

            _linker.DefineFunction("engine", "engine_input_get_axis",
                (int namePtr, int nameLen) =>
                {
                    return InputBridge.GetAxis(_memory, namePtr, nameLen);
                });

            _linker.DefineFunction("engine", "engine_input_is_action_pressed",
                (int actionPtr, int actionLen) =>
                {
                    return InputBridge.IsActionPressed(_memory, actionPtr, actionLen);
                });
        }

        // -----------------------------------------------------------------
        // Physics (12 functions)
        // -----------------------------------------------------------------
        private void RegisterPhysicsImports()
        {
            _linker.DefineFunction("engine", "engine_physics_add_rigidbody",
                (int entity, int bodyType) =>
                {
                    PhysicsBridge.AddRigidbody(entity, bodyType);
                });

            _linker.DefineFunction("engine", "engine_physics_set_mass",
                (int entity, float mass) =>
                {
                    PhysicsBridge.SetMass(entity, mass);
                });

            _linker.DefineFunction("engine", "engine_physics_set_velocity",
                (int entity, float vx, float vy, float vz) =>
                {
                    PhysicsBridge.SetVelocity(entity, vx, vy, vz);
                });

            _linker.DefineFunction("engine", "engine_physics_get_velocity",
                (int entity, int outPtr) =>
                {
                    PhysicsBridge.GetVelocity(_memory, entity, outPtr);
                });

            _linker.DefineFunction("engine", "engine_physics_add_force",
                (int entity, float fx, float fy, float fz) =>
                {
                    PhysicsBridge.AddForce(entity, fx, fy, fz);
                });

            _linker.DefineFunction("engine", "engine_physics_add_impulse",
                (int entity, float ix, float iy, float iz) =>
                {
                    PhysicsBridge.AddImpulse(entity, ix, iy, iz);
                });

            _linker.DefineFunction("engine", "engine_physics_add_collider_box",
                (int entity, float hx, float hy, float hz) =>
                {
                    PhysicsBridge.AddColliderBox(entity, hx, hy, hz);
                });

            _linker.DefineFunction("engine", "engine_physics_add_collider_sphere",
                (int entity, float radius) =>
                {
                    PhysicsBridge.AddColliderSphere(entity, radius);
                });

            _linker.DefineFunction("engine", "engine_physics_add_collider_capsule",
                (int entity, float radius, float height) =>
                {
                    PhysicsBridge.AddColliderCapsule(entity, radius, height);
                });

            _linker.DefineFunction("engine", "engine_physics_raycast",
                (float ox, float oy, float oz, float dx, float dy, float dz,
                 float maxDist, int outPtr) =>
                {
                    return PhysicsBridge.Raycast(_memory, ox, oy, oz, dx, dy, dz,
                                                 maxDist, outPtr);
                });

            _linker.DefineFunction("engine", "engine_physics_set_gravity",
                (float gx, float gy, float gz) =>
                {
                    PhysicsBridge.SetGravity(gx, gy, gz);
                });

            _linker.DefineFunction("engine", "engine_physics_set_collision_layer",
                (int entity, int layer, int mask) =>
                {
                    PhysicsBridge.SetCollisionLayer(entity, layer, mask);
                });
        }

        // -----------------------------------------------------------------
        // Audio (8 functions)
        // -----------------------------------------------------------------
        private void RegisterAudioImports()
        {
            _linker.DefineFunction("engine", "engine_audio_load",
                (int pathPtr, int pathLen) =>
                {
                    return AudioBridge.Load(_memory, pathPtr, pathLen);
                });

            _linker.DefineFunction("engine", "engine_audio_play",
                (int audioId) =>
                {
                    AudioBridge.Play(audioId);
                });

            _linker.DefineFunction("engine", "engine_audio_stop",
                (int audioId) =>
                {
                    AudioBridge.Stop(audioId);
                });

            _linker.DefineFunction("engine", "engine_audio_set_volume",
                (int audioId, float volume) =>
                {
                    AudioBridge.SetVolume(audioId, volume);
                });

            _linker.DefineFunction("engine", "engine_audio_set_pitch",
                (int audioId, float pitch) =>
                {
                    AudioBridge.SetPitch(audioId, pitch);
                });

            _linker.DefineFunction("engine", "engine_audio_set_spatial",
                (int audioId, int entity) =>
                {
                    AudioBridge.SetSpatial(audioId, entity);
                });

            _linker.DefineFunction("engine", "engine_audio_set_position",
                (int audioId, float x, float y, float z) =>
                {
                    AudioBridge.SetPosition(audioId, x, y, z);
                });

            _linker.DefineFunction("engine", "engine_audio_is_playing",
                (int audioId) =>
                {
                    return AudioBridge.IsPlaying(audioId);
                });
        }

        // -----------------------------------------------------------------
        // Asset Management (4 functions)
        // -----------------------------------------------------------------
        private void RegisterAssetImports()
        {
            _linker.DefineFunction("engine", "engine_asset_load",
                (int pathPtr, int pathLen, int assetType) =>
                {
                    string path = ReadString(pathPtr, pathLen);
                    UnityEngine.Object asset = null;

                    switch (assetType)
                    {
                        case 0: // Mesh
                            asset = Resources.Load<Mesh>(path);
                            break;
                        case 1: // Texture
                            asset = Resources.Load<Texture2D>(path);
                            break;
                        case 2: // AudioClip
                            asset = Resources.Load<AudioClip>(path);
                            break;
                        case 3: // Material
                            asset = Resources.Load<Material>(path);
                            break;
                        default:
                            asset = Resources.Load(path);
                            break;
                    }

                    if (asset == null)
                    {
                        Debug.LogWarning($"[SimpleWasm] Asset not found: {path} (type={assetType})");
                        return -1;
                    }

                    return _assets.Add(asset);
                });

            _linker.DefineFunction("engine", "engine_asset_is_loaded",
                (int assetId) =>
                {
                    return _assets.Get(assetId) != null ? 1 : 0;
                });

            _linker.DefineFunction("engine", "engine_asset_unload",
                (int assetId) =>
                {
                    _assets.Remove(assetId);
                });

            _linker.DefineFunction("engine", "engine_asset_load_texture",
                (int pathPtr, int pathLen) =>
                {
                    string path = ReadString(pathPtr, pathLen);
                    var tex = Resources.Load<Texture2D>(path);
                    if (tex == null)
                    {
                        Debug.LogWarning($"[SimpleWasm] Texture not found: {path}");
                        return -1;
                    }
                    return _assets.Add(tex);
                });
        }

        // -----------------------------------------------------------------
        // Debug (2 functions)
        // -----------------------------------------------------------------
        private void RegisterDebugImports()
        {
            _linker.DefineFunction("engine", "engine_debug_log",
                (int msgPtr, int msgLen) =>
                {
                    string msg = ReadString(msgPtr, msgLen);
                    Debug.Log($"[WASM] {msg}");
                });

            _linker.DefineFunction("engine", "engine_debug_draw_line",
                (float x1, float y1, float z1, float x2, float y2, float z2,
                 float r, float g, float b) =>
                {
                    Debug.DrawLine(
                        new Vector3(x1, y1, z1),
                        new Vector3(x2, y2, z2),
                        new Color(r, g, b),
                        0f   // duration: one frame
                    );
                });
        }
    }

    // =====================================================================
    // Wasmtime Memory extension helpers
    // =====================================================================

    /// <summary>
    /// Extension methods for reading/writing typed values from WASM linear memory.
    /// </summary>
    public static class MemoryExtensions
    {
        public static void WriteFloat(this Memory memory, int offset, float value)
        {
            var span = memory.GetSpan<byte>();
            BitConverter.TryWriteBytes(span.Slice(offset, 4), value);
        }

        public static float ReadFloat(this Memory memory, int offset)
        {
            var span = memory.GetSpan<byte>();
            return BitConverter.ToSingle(span.Slice(offset, 4));
        }

        public static string ReadString(this Memory memory, int offset, int length)
        {
            if (length <= 0) return "";
            var span = memory.GetSpan<byte>().Slice(offset, length);
            return Encoding.UTF8.GetString(span);
        }
    }
}
