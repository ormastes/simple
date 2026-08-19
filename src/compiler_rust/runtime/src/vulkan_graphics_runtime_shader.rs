#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, ComputePipeline, ShaderModule, STATE};
#[cfg(feature = "vulkan")]
use crate::value::heap::with_typed_ptr;
#[cfg(feature = "vulkan")]
use crate::value::{byte_array_bytes, rt_interp_cstr, HeapObjectType, RuntimeString, RuntimeValue};
#[cfg(feature = "vulkan")]
use std::ffi::CStr;
#[cfg(feature = "vulkan")]
use std::os::raw::c_char;
#[cfg(feature = "vulkan")]
use std::sync::Arc;

#[cfg(feature = "vulkan")]
fn runtime_entry_name(value_raw: i64) -> Result<String, String> {
    let value = RuntimeValue::from_raw(value_raw as u64);
    if value.is_heap() {
        if let Some(bytes) = with_typed_ptr(
            value,
            HeapObjectType::String,
            |string_ptr: *const RuntimeString| unsafe { (*string_ptr).as_bytes().to_vec() },
        ) {
            return std::str::from_utf8(&bytes)
                .map(str::to_owned)
                .map_err(|_| "entry name: RuntimeString is not valid UTF-8".to_string());
        }
    }

    let cstr = rt_interp_cstr(value) as *const c_char;
    if cstr.is_null() {
        return Err("entry name: null C string".to_string());
    }
    unsafe { CStr::from_ptr(cstr) }
        .to_str()
        .map(str::to_owned)
        .map_err(|_| "entry name: C string is not valid UTF-8".to_string())
}

// ============================================================================
// Shader & Pipeline
// ============================================================================

/// Create a `ShaderModule` from a native Simple `[u8]` value.
#[cfg(feature = "vulkan")]
fn compile_spirv_bytes(spirv_bytes: Vec<u8>) -> i64 {
    let len = spirv_bytes.len();
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    if len < 20 || len > 64 * 1024 * 1024 || len % 4 != 0 {
        state.set_error("compile_spirv: invalid byte length".to_string());
        return 0;
    }
    let magic = u32::from_le_bytes(spirv_bytes[..4].try_into().unwrap());
    if magic != 0x07230203 {
        state.set_error(format!("compile_spirv: bad SPIR-V magic 0x{magic:08x}"));
        return 0;
    }

    let spirv_owned = spirv_bytes.clone();

    match ShaderModule::new(device, &spirv_bytes) {
        Ok(module) => {
            let h = alloc_handle();
            state.shader_modules.insert(h, module);
            state.shader_spirv.insert(h, spirv_owned);
            h
        }
        Err(e) => {
            state.set_error(format!("compile_spirv: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_spirv(spirv: RuntimeValue) -> i64 {
    let Some(spirv_bytes) = byte_array_bytes(spirv) else {
        return 0;
    };
    compile_spirv_bytes(spirv_bytes)
}

/// AOT/raw-array ABI for pure-Simple native executables.
///
/// The tagged `RuntimeValue` entry remains the interpreter/JIT ABI. Native
/// Simple `[u8]` values use the core-C array layout, so their data pointer and
/// byte count must cross the provider boundary explicitly.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_spirv_raw(data_ptr: i64, byte_count: i64) -> i64 {
    if data_ptr <= 0 || byte_count < 20 || byte_count > 64 * 1024 * 1024 || byte_count % 4 != 0 {
        return 0;
    }
    let bytes = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, byte_count as usize).to_vec() };
    compile_spirv_bytes(bytes)
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_spirv(_spirv: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_spirv_raw(_data_ptr: i64, _byte_count: i64) -> i64 {
    0
}

/// Call-scoped packed SPIR-V input; no address is returned to Simple.
#[no_mangle]
pub extern "C" fn rt_vulkan_compile_spirv_array(data: RuntimeValue) -> i64 {
    let Some(bytes) = byte_array_bytes(data) else {
        return 0;
    };
    rt_vulkan_compile_spirv_raw(bytes.as_ptr() as i64, bytes.len() as i64)
}

#[cfg(all(test, feature = "vulkan"))]
mod raw_guard_tests {
    use super::{
        rt_vulkan_compile_spirv_raw, rt_vulkan_create_compute_pipeline, rt_vulkan_destroy_pipeline,
        rt_vulkan_destroy_shader, runtime_entry_name,
    };
    use crate::value::{rt_string_free, rt_string_new};
    use crate::vulkan_graphics_runtime::vulkan_graphics_runtime_core::{rt_vulkan_init, rt_vulkan_shutdown};
    use std::ffi::CString;

    #[test]
    fn vulkan_raw_guard_rejects_invalid_spirv_length_before_pointer_access() {
        assert_eq!(rt_vulkan_compile_spirv_raw(1, 3), 0);
        assert_eq!(rt_vulkan_compile_spirv_raw(1, 22), 0);
    }

    #[test]
    fn vulkan_pipeline_entry_reads_runtime_and_raw_strings_exactly() {
        let name = "custom_compute_entry";
        let runtime = rt_string_new(name.as_ptr(), name.len() as u64);
        assert_eq!(runtime_entry_name(runtime.to_raw() as i64), Ok(name.to_string()));
        assert_eq!(rt_string_free(runtime), 1);

        let raw = CString::new("raw_compute_entry").unwrap();
        assert_eq!(
            runtime_entry_name(raw.as_ptr() as i64),
            Ok("raw_compute_entry".to_string())
        );

        #[repr(align(8))]
        struct AlignedEntry([u8; 19]);
        let tagged_raw = AlignedEntry(*b"_aligned_raw_entry\0");
        let tagged_raw_ptr = unsafe { tagged_raw.0.as_ptr().add(1) };
        assert_eq!((tagged_raw_ptr as usize) & 7, 1);
        assert_eq!(
            runtime_entry_name(tagged_raw_ptr as i64),
            Ok("aligned_raw_entry".to_string())
        );
        assert!(runtime_entry_name(0).is_err());
    }

    #[test]
    #[ignore = "requires a Vulkan device"]
    fn vulkan_pipeline_creates_non_main_spirv_entry_on_available_device() {
        assert_eq!(rt_vulkan_init(), 1, "live Vulkan device is required");

        let words: [u32; 42] = [
            119734787, 67072, 458752, 5, 0, 131089, 1, 196622, 0, 1, 589839, 5, 1, 1953723747, 1667198319, 1970302319,
            1700750708, 2037544046, 0, 393232, 1, 17, 1, 1, 1, 196611, 2, 450, 131091, 2, 196641, 3, 2, 327734, 2, 1,
            0, 3, 131320, 4, 65789, 65592,
        ];
        let spirv: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
        let shader = rt_vulkan_compile_spirv_raw(spirv.as_ptr() as i64, spirv.len() as i64);
        assert_ne!(shader, 0);

        let wrong = CString::new("main").unwrap();
        assert_eq!(rt_vulkan_create_compute_pipeline(shader, wrong.as_ptr() as i64, 0), 0);

        let entry = CString::new("custom_compute_entry").unwrap();
        let pipeline = rt_vulkan_create_compute_pipeline(shader, entry.as_ptr() as i64, 0);
        assert_ne!(pipeline, 0);
        assert_eq!(rt_vulkan_destroy_pipeline(pipeline), 1);
        assert_eq!(rt_vulkan_destroy_shader(shader), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }
}

// ──────────────────────────────────────────────────────────────────────────────

/// GLSL compilation stub — GLSL→SPIR-V requires shaderc/glslang integration.
/// Use `rt_vulkan_compile_spirv` with pre-compiled SPIR-V instead.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_glsl(_source: i64) -> i64 {
    let mut state = STATE.lock();
    state.set_error("GLSL compilation not supported. Use pre-compiled SPIR-V via rt_vulkan_compile_spirv.".to_string());
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_glsl(_source: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_shader(module: i64) -> i64 {
    let mut state = STATE.lock();
    state.shader_spirv.remove(&module);
    if state.shader_modules.remove(&module).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_shader(_module: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Create a compute pipeline.
///
/// `shader` is the handle from `rt_vulkan_compile_spirv`.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_compute_pipeline(shader: i64, entry: i64, push_size: i64) -> i64 {
    let mut state = STATE.lock();
    if !(0..=u32::MAX as i64).contains(&push_size) {
        state.set_error("create_compute_pipeline: push size is outside u32 range".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    if shader == 0 {
        state.set_error("create_compute_pipeline: null shader".to_string());
        return 0;
    }

    let Some(spirv_owned) = state.shader_spirv.get(&shader).cloned() else {
        state.set_error("create_compute_pipeline: unknown shader handle".to_string());
        return 0;
    };

    let entry_name = match runtime_entry_name(entry) {
        Ok(name) => name,
        Err(e) => {
            state.set_error(format!("create_compute_pipeline: {e}"));
            return 0;
        }
    };

    match ComputePipeline::new(device, &spirv_owned, &entry_name, push_size as u32) {
        Ok(pipe) => {
            let h = alloc_handle();
            state.compute_pipelines.insert(h, Arc::new(pipe));
            h
        }
        Err(e) => {
            state.set_error(format!("create_compute_pipeline: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_compute_pipeline(_shader: i64, _entry: i64, _push_size: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_pipeline(pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let removed_compute = state.compute_pipelines.remove(&pipe).is_some();
    let removed_graphics = state.graphics_pipelines.remove(&pipe).is_some();
    if removed_compute || removed_graphics {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_pipeline(_pipe: i64) -> i64 {
    0
}
#[cfg(not(feature = "vulkan"))]
use crate::value::{byte_array_bytes, RuntimeValue};
