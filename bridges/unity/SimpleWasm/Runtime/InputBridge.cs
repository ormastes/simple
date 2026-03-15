using UnityEngine;
using Wasmtime;

namespace SimpleWasm
{
    /// <summary>
    /// Implements the 8 engine_input_* WASM ABI functions.
    /// All bool results are returned as i32 (0 or 1).
    /// Out-pointer pattern: writes f32 values into WASM linear memory.
    /// </summary>
    public static class InputBridge
    {
        /// <summary>
        /// Map Simple key code integers to Unity KeyCode.
        /// Simple uses a sequential numbering scheme; this maps the common ones.
        /// </summary>
        private static KeyCode MapKeyCode(int key)
        {
            // Letters: 0-25 -> A-Z
            if (key >= 0 && key <= 25)
                return (KeyCode)((int)KeyCode.A + key);

            // Digits: 26-35 -> Alpha0-Alpha9
            if (key >= 26 && key <= 35)
                return (KeyCode)((int)KeyCode.Alpha0 + (key - 26));

            // Function keys: 36-47 -> F1-F12
            if (key >= 36 && key <= 47)
                return (KeyCode)((int)KeyCode.F1 + (key - 36));

            // Special keys
            switch (key)
            {
                case 100: return KeyCode.Space;
                case 101: return KeyCode.Return;
                case 102: return KeyCode.Escape;
                case 103: return KeyCode.Tab;
                case 104: return KeyCode.Backspace;
                case 105: return KeyCode.Delete;
                case 106: return KeyCode.LeftShift;
                case 107: return KeyCode.RightShift;
                case 108: return KeyCode.LeftControl;
                case 109: return KeyCode.RightControl;
                case 110: return KeyCode.LeftAlt;
                case 111: return KeyCode.RightAlt;
                case 112: return KeyCode.UpArrow;
                case 113: return KeyCode.DownArrow;
                case 114: return KeyCode.LeftArrow;
                case 115: return KeyCode.RightArrow;
                default:  return KeyCode.None;
            }
        }

        /// <summary>
        /// engine_input_is_key_pressed(key_code: i32) -> i32
        /// </summary>
        public static int IsKeyPressed(int keyCode)
        {
            return Input.GetKey(MapKeyCode(keyCode)) ? 1 : 0;
        }

        /// <summary>
        /// engine_input_is_key_just_pressed(key_code: i32) -> i32
        /// </summary>
        public static int IsKeyJustPressed(int keyCode)
        {
            return Input.GetKeyDown(MapKeyCode(keyCode)) ? 1 : 0;
        }

        /// <summary>
        /// engine_input_is_key_just_released(key_code: i32) -> i32
        /// </summary>
        public static int IsKeyJustReleased(int keyCode)
        {
            return Input.GetKeyUp(MapKeyCode(keyCode)) ? 1 : 0;
        }

        /// <summary>
        /// engine_input_get_mouse_position(out_ptr: i32)
        /// Writes 2 floats (x, y) to WASM memory at out_ptr.
        /// </summary>
        public static void GetMousePosition(Memory memory, int outPtr)
        {
            Vector3 pos = Input.mousePosition;
            memory.WriteFloat(outPtr, pos.x);
            memory.WriteFloat(outPtr + 4, pos.y);
        }

        /// <summary>
        /// engine_input_get_mouse_delta(out_ptr: i32)
        /// Writes 2 floats (dx, dy) to WASM memory at out_ptr.
        /// </summary>
        public static void GetMouseDelta(Memory memory, int outPtr)
        {
            float dx = Input.GetAxis("Mouse X");
            float dy = Input.GetAxis("Mouse Y");
            memory.WriteFloat(outPtr, dx);
            memory.WriteFloat(outPtr + 4, dy);
        }

        /// <summary>
        /// engine_input_is_mouse_button_pressed(button: i32) -> i32
        /// </summary>
        public static int IsMouseButtonPressed(int button)
        {
            return Input.GetMouseButton(button) ? 1 : 0;
        }

        /// <summary>
        /// engine_input_get_axis(axis_name_ptr: i32, axis_name_len: i32) -> f32
        /// </summary>
        public static float GetAxis(Memory memory, int namePtr, int nameLen)
        {
            string axisName = memory.ReadString(namePtr, nameLen);
            try
            {
                return Input.GetAxis(axisName);
            }
            catch
            {
                Debug.LogWarning($"[SimpleWasm] Unknown input axis: {axisName}");
                return 0f;
            }
        }

        /// <summary>
        /// engine_input_is_action_pressed(action_ptr: i32, action_len: i32) -> i32
        /// </summary>
        public static int IsActionPressed(Memory memory, int actionPtr, int actionLen)
        {
            string action = memory.ReadString(actionPtr, actionLen);
            try
            {
                return Input.GetButton(action) ? 1 : 0;
            }
            catch
            {
                Debug.LogWarning($"[SimpleWasm] Unknown input action: {action}");
                return 0;
            }
        }
    }
}
