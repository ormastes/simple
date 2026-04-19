#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, ComputePipeline, ShaderModule, STATE};

// ============================================================================
// Shader & Pipeline
// ============================================================================

/// Create a `ShaderModule` from raw SPIR-V bytes.
///
/// `spirv_ptr` is treated as `*const u8`; length is inferred from the SPIR-V
/// header by scanning instruction words up to 64 MiB.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_spirv(spirv_ptr: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    if spirv_ptr == 0 {
        state.set_error("compile_spirv: null pointer".to_string());
        return 0;
    }

    let base = spirv_ptr as *const u8;
    let magic = unsafe { *(base as *const u32) };
    if magic != 0x07230203 {
        state.set_error(format!("compile_spirv: bad SPIR-V magic 0x{magic:08x}"));
        return 0;
    }

    let spirv_bytes = read_spirv_bytes(base);

    match ShaderModule::new(device, spirv_bytes) {
        Ok(module) => {
            let h = alloc_handle();
            state.shader_modules.insert(h, module);
            h
        }
        Err(e) => {
            state.set_error(format!("compile_spirv: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_spirv(_spirv: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// GLSL compilation stub — GLSL→SPIR-V requires shaderc/glslang integration.
/// Use `rt_vulkan_compile_spirv` with pre-compiled SPIR-V instead.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_glsl(_source: i64) -> i64 {
    let mut state = STATE.lock();
    state.set_error(
        "GLSL compilation not supported. Use pre-compiled SPIR-V via rt_vulkan_compile_spirv."
            .to_string(),
    );
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
    if state.shader_modules.remove(&module).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_shader(_module: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Create a compute pipeline.
///
/// `shader` is the handle from `rt_vulkan_compile_spirv`, or a raw SPIR-V
/// pointer. `entry` and `push_size` are currently unused.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_compute_pipeline(shader: i64, _entry: i64, _push_size: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    if state.shader_modules.contains_key(&shader) {
        // TODO: cache SPIR-V bytes alongside the shader module handle.
        state.set_error(
            "create_compute_pipeline: pass raw SPIR-V pointer via compile_spirv handle \
             is not yet supported; pass SPIR-V bytes directly"
                .to_string(),
        );
        return 0;
    }

    if shader == 0 {
        state.set_error("create_compute_pipeline: null shader".to_string());
        return 0;
    }

    let base = shader as *const u8;
    let magic = unsafe { *(base as *const u32) };
    if magic != 0x07230203 {
        state.set_error(format!("create_compute_pipeline: bad SPIR-V magic 0x{magic:08x}"));
        return 0;
    }

    let spirv_bytes = read_spirv_bytes(base);

    match ComputePipeline::new(device, spirv_bytes) {
        Ok(pipe) => {
            let h = alloc_handle();
            state.compute_pipelines.insert(h, pipe);
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
    if removed_compute || removed_graphics { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_pipeline(_pipe: i64) -> i64 {
    0
}

// ── Internal helper ──────────────────────────────────────────────────────────

/// Read SPIR-V bytes from a raw pointer by scanning instruction words (up to 64 MiB).
#[cfg(feature = "vulkan")]
fn read_spirv_bytes(base: *const u8) -> &'static [u8] {
    let max_len: usize = 64 * 1024 * 1024;
    let spirv_slice = unsafe { std::slice::from_raw_parts(base, max_len) };
    let mut pos = 5 * 4; // skip 5-word header
    loop {
        if pos + 4 > max_len {
            break;
        }
        let word = u32::from_le_bytes([
            spirv_slice[pos],
            spirv_slice[pos + 1],
            spirv_slice[pos + 2],
            spirv_slice[pos + 3],
        ]);
        let wc = (word >> 16) as usize;
        if wc == 0 {
            break;
        }
        let advance = wc * 4;
        if pos + advance > max_len {
            break;
        }
        pos += advance;
    }
    unsafe { std::slice::from_raw_parts(base, pos) }
}
