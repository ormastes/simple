using UnityEngine;
using Wasmtime;

namespace SimpleWasm
{
    /// <summary>
    /// Implements the 8 engine_audio_* WASM ABI functions.
    /// Audio clips are loaded from Resources and managed via HandleTable.
    /// Each audio handle maps to a dedicated AudioSource on a pooled GameObject.
    /// </summary>
    public static class AudioBridge
    {
        /// <summary>
        /// Handle table for audio sources. Set by WasmBridge on init.
        /// </summary>
        public static HandleTable<AudioSource> Sources { get; set; }

        /// <summary>
        /// Shared entity table for spatial audio attachment. Set by WasmBridge on init.
        /// </summary>
        public static HandleTable<GameObject> Entities { get; set; }

        /// <summary>
        /// Parent transform for audio source GameObjects.
        /// </summary>
        public static Transform AudioRoot { get; set; }

        /// <summary>
        /// engine_audio_load(path_ptr: i32, path_len: i32) -> i32
        /// Loads an AudioClip from Resources and creates an AudioSource.
        /// Returns a handle to the audio source, or -1 on failure.
        /// </summary>
        public static int Load(Memory memory, int pathPtr, int pathLen)
        {
            string path = memory.ReadString(pathPtr, pathLen);

            // Strip file extension if present (Resources.Load doesn't want it)
            if (path.EndsWith(".wav") || path.EndsWith(".ogg") || path.EndsWith(".mp3"))
                path = path.Substring(0, path.LastIndexOf('.'));

            AudioClip clip = Resources.Load<AudioClip>(path);
            if (clip == null)
            {
                Debug.LogWarning($"[SimpleWasm] Failed to load audio clip: {path}");
                return -1;
            }

            var audioGo = new GameObject($"SimpleWasm_Audio_{path}");
            if (AudioRoot != null)
                audioGo.transform.SetParent(AudioRoot);

            var source = audioGo.AddComponent<AudioSource>();
            source.clip = clip;
            source.playOnAwake = false;

            return Sources.Add(source);
        }

        /// <summary>
        /// engine_audio_play(audio_id: i32)
        /// </summary>
        public static void Play(int audioId)
        {
            var source = Sources.Get(audioId);
            if (source != null) source.Play();
        }

        /// <summary>
        /// engine_audio_stop(audio_id: i32)
        /// </summary>
        public static void Stop(int audioId)
        {
            var source = Sources.Get(audioId);
            if (source != null) source.Stop();
        }

        /// <summary>
        /// engine_audio_set_volume(audio_id: i32, volume: f32)
        /// </summary>
        public static void SetVolume(int audioId, float volume)
        {
            var source = Sources.Get(audioId);
            if (source != null) source.volume = Mathf.Clamp01(volume);
        }

        /// <summary>
        /// engine_audio_set_pitch(audio_id: i32, pitch: f32)
        /// </summary>
        public static void SetPitch(int audioId, float pitch)
        {
            var source = Sources.Get(audioId);
            if (source != null) source.pitch = pitch;
        }

        /// <summary>
        /// engine_audio_set_spatial(audio_id: i32, entity: i32)
        /// Attaches the audio source to an entity's GameObject for 3D spatialization.
        /// </summary>
        public static void SetSpatial(int audioId, int entity)
        {
            var source = Sources.Get(audioId);
            var go = Entities.Get(entity);
            if (source == null || go == null) return;

            source.spatialBlend = 1.0f; // fully 3D
            source.transform.SetParent(go.transform);
            source.transform.localPosition = Vector3.zero;
        }

        /// <summary>
        /// engine_audio_set_position(audio_id: i32, x: f32, y: f32, z: f32)
        /// Sets the world position of the audio source (for non-attached spatial audio).
        /// </summary>
        public static void SetPosition(int audioId, float x, float y, float z)
        {
            var source = Sources.Get(audioId);
            if (source == null) return;

            source.spatialBlend = 1.0f;
            source.transform.position = new Vector3(x, y, z);
        }

        /// <summary>
        /// engine_audio_is_playing(audio_id: i32) -> i32
        /// </summary>
        public static int IsPlaying(int audioId)
        {
            var source = Sources.Get(audioId);
            return (source != null && source.isPlaying) ? 1 : 0;
        }
    }
}
