using UnityEditor;
using UnityEngine;

namespace SimpleWasm.Editor
{
    /// <summary>
    /// Custom inspector for the WasmBridge MonoBehaviour.
    /// Shows WASM file selector, reload button, and module state.
    /// </summary>
    [CustomEditor(typeof(WasmBridge))]
    public class SimpleWasmInspector : UnityEditor.Editor
    {
        public override void OnInspectorGUI()
        {
            var bridge = (WasmBridge)target;

            // Draw default fields (wasmPath, etc.)
            DrawDefaultInspector();

            EditorGUILayout.Space();

            // WASM file picker
            EditorGUILayout.LabelField("WASM Module", EditorStyles.boldLabel);

            if (GUILayout.Button("Browse for .wasm file"))
            {
                string path = EditorUtility.OpenFilePanel("Select WASM Module", "", "wasm");
                if (!string.IsNullOrEmpty(path))
                {
                    Undo.RecordObject(bridge, "Set WASM Path");
                    var serializedPath = serializedObject.FindProperty("wasmPath");
                    serializedPath.stringValue = path;
                    serializedObject.ApplyModifiedProperties();
                }
            }

            EditorGUILayout.Space();

            // Runtime controls
            EditorGUILayout.LabelField("Runtime", EditorStyles.boldLabel);

            bool isLoaded = Application.isPlaying && bridge.IsLoaded;
            EditorGUILayout.LabelField("Status", isLoaded ? "Loaded" : "Not Loaded");

            if (Application.isPlaying)
            {
                if (isLoaded)
                {
                    EditorGUILayout.LabelField("Entity Count", bridge.EntityCount.ToString());
                }

                EditorGUILayout.Space();

                if (GUILayout.Button("Reload WASM"))
                {
                    bridge.ReloadWasm();
                }
            }
            else
            {
                EditorGUILayout.HelpBox(
                    "Enter Play Mode to load the WASM module.",
                    MessageType.Info);
            }
        }
    }
}
