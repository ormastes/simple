# Vulkan API Implementation Mapping

**Date:** 2025-12-27
**Purpose:** Map Simple stdlib API declarations to Rust FFI implementations

---

## Overview

The Simple language Vulkan API is defined in `simple/std_lib/src/ui/gui/vulkan_types.spl` with extern function declarations. This document tracks which functions are implemented in the Rust runtime FFI layer.

**Implementation Status:**
- ✅ **Implemented** - Function exists and works
- ⚠️ **Partial** - Function exists but has limitations
- ⏳ **Stub** - Function exists but returns NotSupported
- ❌ **Missing** - Function not yet implemented

---

## FFI Function Mapping

### Instance and Device Creation

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_create_instance` | Not needed | N/A | Instance is singleton, auto-created |
| `vulkan_enumerate_physical_devices` | Not needed | N/A | Device selection handled internally |
| `vulkan_create_device` | `rt_vk_device_create` | ✅ Implemented | Returns device handle |
| `vulkan_get_device_queue` | Not exposed | N/A | Queues managed internally |

**Notes:**
- Instance creation is automatic via `VulkanInstance::get_or_init()`
- Device selection prefers discrete GPU automatically
- Queue management is internal to VulkanDevice

---

### Device Queries

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_get_physical_device_properties` | Not exposed | ❌ Missing | Could add for device info |
| `vulkan_get_physical_device_features` | Not exposed | ❌ Missing | Could add for capability queries |
| `vulkan_get_physical_device_memory_properties` | Not exposed | ❌ Missing | Internal use only |
| `vulkan_get_physical_device_queue_families` | Not exposed | ❌ Missing | Internal use only |
| `vulkan_queue_family_supports_present` | Not exposed | ❌ Missing | Internal use only |

**Notes:**
- Device properties currently internal-only
- Could expose for Simple language to query GPU capabilities
- Low priority - applications rarely need this info

---

### Surface Operations

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_get_surface_capabilities` | Not exposed | ❌ Missing | Handled by Surface internally |
| `vulkan_get_surface_formats` | Not exposed | ❌ Missing | Automatic selection |
| `vulkan_get_surface_present_modes` | Not exposed | ❌ Missing | Automatic selection |

**Notes:**
- Surface creation tied to window creation
- Format/mode selection uses smart defaults
- HDR support through `prefer_hdr` parameter in swapchain creation

---

### Window Management

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| (Not in vulkan_types.spl) | `rt_vk_window_create` | ✅ Implemented | Creates window with surface, initializes event loop thread |
| (Not in vulkan_types.spl) | `rt_vk_window_destroy` | ✅ Implemented | Destroys window and cleans up surface |
| (Not in vulkan_types.spl) | `rt_vk_window_get_size` | ✅ Implemented | Queries window dimensions |
| (Not in vulkan_types.spl) | `rt_vk_window_set_fullscreen` | ✅ Implemented | Sets fullscreen mode (windowed/borderless/exclusive) |
| (Not in vulkan_types.spl) | `rt_vk_window_poll_event` | ✅ Implemented | Non-blocking event polling (7 event types) |
| (Not in vulkan_types.spl) | `rt_vk_window_wait_event` | ✅ Implemented | Blocking event wait with timeout |

**Notes:**
- Window API not yet defined in Simple stdlib (needs wrapper layer)
- Event loop architecture fixed (see VULKAN_EVENT_LOOP_FIX_2025-12-27.md)
- FFI implementation complete (see VULKAN_WINDOW_FFI_2025-12-27.md)
- Ready for Simple language integration

---

### Swapchain Operations

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_create_swapchain` | `rt_vk_swapchain_create` | ✅ Implemented | Full swapchain creation with HDR support |
| `vulkan_get_swapchain_images` | `rt_vk_swapchain_get_image_count` | ✅ Implemented | Returns count, not images themselves |
| `vulkan_create_image_view` | Not exposed | N/A | Image views created automatically |
| `vulkan_acquire_next_image` | `rt_vk_swapchain_acquire_next_image` | ✅ Implemented | Async image acquisition |
| (Not in vulkan_types.spl) | `rt_vk_swapchain_recreate` | ⚠️ Partial | Returns NotSupported, needs Arc<Mutex<>> |
| (Not in vulkan_types.spl) | `rt_vk_swapchain_destroy` | ✅ Implemented | Full cleanup |
| (Not in vulkan_types.spl) | `rt_vk_swapchain_present` | ✅ Implemented | Image presentation to screen |
| (Not in vulkan_types.spl) | `rt_vk_swapchain_get_extent` | ✅ Implemented | Query swapchain dimensions |

**Signatures:**
```c
i64 rt_vk_swapchain_create(device_handle, surface_handle, width, height, prefer_hdr, prefer_no_vsync)
i32 rt_vk_swapchain_recreate(swapchain_handle, surface_handle, width, height)  // NotSupported
i32 rt_vk_swapchain_destroy(swapchain_handle)
i32 rt_vk_swapchain_acquire_next_image(swapchain_handle, timeout_ns, out_suboptimal)
i32 rt_vk_swapchain_present(swapchain_handle, image_index)
i32 rt_vk_swapchain_get_image_count(swapchain_handle)
i32 rt_vk_swapchain_get_extent(swapchain_handle, out_width, out_height)
```

**Notes:**
- Recreation blocked by Arc<Mutex<>> requirement (see Known Issues)
- HDR support via `prefer_hdr` parameter
- Triple buffering by default

---

### Render Pass Operations

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_create_render_pass` | Not exposed | ❌ Missing | Module exists, FFI not yet added |

**Implementation:**
- `RenderPass::new_simple()` - Single color attachment
- `RenderPass::new_with_depth()` - Color + depth attachments
- **TODO:** Add FFI wrapper functions

---

### Synchronization

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_device_wait_idle` | Not exposed | ❌ Missing | Device has internal wait_idle() |
| `vulkan_wait_for_fence` | Not exposed | ❌ Missing | Fence has wait() method |
| `vulkan_reset_fence` | Not exposed | ❌ Missing | Fence has reset() method |
| `vulkan_create_fence` | `rt_vk_fence_create` | ✅ Implemented | Creates fence with signaled state |
| `vulkan_create_semaphore` | `rt_vk_semaphore_create` | ✅ Implemented | Creates binary semaphore |

**Signatures:**
```c
i64 rt_vk_fence_create(device_handle, signaled)
i32 rt_vk_fence_wait(fence_handle, timeout_ns)
i32 rt_vk_fence_reset(fence_handle)
i32 rt_vk_fence_destroy(fence_handle)

i64 rt_vk_semaphore_create(device_handle)
i32 rt_vk_semaphore_destroy(semaphore_handle)
```

**Notes:**
- Fence and Semaphore have full implementations
- Registries: FENCE_REGISTRY, SEMAPHORE_REGISTRY
- SemaphorePool available for efficient allocation

---

### Command Buffer Operations

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_allocate_command_buffer` | Not exposed | ❌ Missing | Not yet implemented |
| `vulkan_reset_command_buffer` | Not exposed | ❌ Missing | Not yet implemented |

**Notes:**
- Command buffer API not yet implemented
- Required for rendering operations
- Medium priority for next phase

---

### Queue Operations

| Simple API | Rust FFI Function | Status | Notes |
|-----------|-------------------|--------|-------|
| `vulkan_queue_present` | `rt_vk_swapchain_present` | ✅ Implemented | Presents via swapchain handle |

**Notes:**
- Queue management is internal
- Present operation exposed through swapchain API

---

## Additional Implemented FFI (Not in vulkan_types.spl)

### Graphics Pipeline

| Rust FFI Function | Status | Purpose |
|-------------------|--------|---------|
| `rt_vk_shader_module_create` | ❌ Missing | Load SPIR-V shader |
| `rt_vk_graphics_pipeline_create` | ❌ Missing | Create graphics pipeline |
| `rt_vk_pipeline_destroy` | ❌ Missing | Cleanup pipeline |

**Implementation:**
- `ShaderModule::new()` - SPIR-V loading with alignment validation
- `GraphicsPipeline::new()` - Full pipeline state object
- **TODO:** Add FFI wrapper functions

---

### Descriptor Sets

| Rust FFI Function | Status | Purpose |
|-------------------|--------|---------|
| `rt_vk_descriptor_layout_create` | ❌ Missing | Create descriptor set layout |
| `rt_vk_descriptor_pool_create` | ❌ Missing | Create descriptor pool |
| `rt_vk_descriptor_set_allocate` | ❌ Missing | Allocate descriptor set |
| `rt_vk_descriptor_set_update_buffer` | ❌ Missing | Update buffer binding |
| `rt_vk_descriptor_set_update_image` | ❌ Missing | Update image binding |

**Implementation:**
- `DescriptorSetLayout::new()` - Layout with bindings
- `DescriptorSetLayout::new_uniform_buffer()` - Uniform buffer layout
- `DescriptorSetLayout::new_combined_image_sampler()` - Sampler layout
- `DescriptorPool::new()` - Pool with type counts
- `DescriptorSet::new()` - Allocate from pool
- `DescriptorSet::update_buffer()` - Update buffer binding
- `DescriptorSet::update_image_sampler()` - Update image binding
- **TODO:** Add FFI wrapper functions

---

### Framebuffers

| Rust FFI Function | Status | Purpose |
|-------------------|--------|---------|
| `rt_vk_framebuffer_create` | ❌ Missing | Create single framebuffer |
| `rt_vk_framebuffer_create_for_swapchain` | ❌ Missing | Create framebuffers for all swapchain images |
| `rt_vk_framebuffer_destroy` | ❌ Missing | Cleanup framebuffer |

**Implementation:**
- `Framebuffer::new()` - Single framebuffer
- `Framebuffer::create_for_swapchain()` - Batch creation
- **TODO:** Add FFI wrapper functions

---

## Implementation Summary

### By Category

| Category | Implemented | Partial | Stub | Missing | Total |
|----------|-------------|---------|------|---------|-------|
| Device | 1 | 0 | 0 | 3 | 4 |
| Surface | 0 | 0 | 0 | 3 | 3 |
| Window | 6 | 0 | 0 | 0 | 6 |
| Swapchain | 6 | 1 | 0 | 0 | 7 |
| Render Pass | 0 | 0 | 0 | 1 | 1 |
| Synchronization | 5 | 0 | 0 | 3 | 8 |
| Command Buffers | 0 | 0 | 0 | 2 | 2 |
| Queue | 1 | 0 | 0 | 0 | 1 |
| Graphics Pipeline | 0 | 0 | 0 | 3 | 3 |
| Descriptors | 0 | 0 | 0 | 5 | 5 |
| Framebuffers | 0 | 0 | 0 | 3 | 3 |
| **Total** | **19** | **1** | **0** | **19** | **39** |

**Completion:** 49% (19/39 fully implemented, +6 window functions)

---

## Priority Recommendations

### ✅ Completed

1. **Event Loop Refactoring** ✅
   - Fixed window FFI stubs
   - Enabled window creation from Simple
   - Implemented all 6 window FFI functions
   - **Status:** Complete (see VULKAN_EVENT_LOOP_FIX_2025-12-27.md, VULKAN_WINDOW_FFI_2025-12-27.md)

### High Priority (Required for Basic Rendering)

2. **Graphics Pipeline FFI** (1 day)
   - `rt_vk_shader_module_create`
   - `rt_vk_graphics_pipeline_create`
   - **Blocks:** Shader loading, pipeline creation

3. **Render Pass FFI** (0.5 days)
   - `rt_vk_render_pass_create`
   - **Blocks:** Rendering setup

4. **Framebuffer FFI** (0.5 days)
   - `rt_vk_framebuffer_create_for_swapchain`
   - **Blocks:** Rendering targets

5. **Descriptor Set FFI** (1 day)
   - All 5 descriptor functions
   - **Blocks:** Uniform buffers, textures

### Medium Priority (Enhances Functionality)

6. **Command Buffer FFI** (1 day)
   - `rt_vk_allocate_command_buffer`
   - `rt_vk_reset_command_buffer`
   - **Blocks:** Recording rendering commands

7. **Swapchain Recreation** (1 day)
   - Fix `rt_vk_swapchain_recreate`
   - Refactor to Arc<Mutex<>>
   - **Improves:** Window resize support

8. **Device Query FFI** (0.5 days)
   - Expose device properties
   - Expose device features
   - **Improves:** GPU capability detection

### Low Priority (Nice to Have)

9. **Surface Query FFI** (0.5 days)
   - Expose surface capabilities
   - Expose format/mode lists
   - **Improves:** Advanced swapchain configuration

10. **Synchronization FFI** (0.5 days)
    - `rt_vk_device_wait_idle`
    - `rt_vk_fence_wait` (currently internal)
    - **Improves:** Fine-grained sync control

---

## Mapping to Simple API Design

### Current Design (vulkan_types.spl)

The Simple API follows a **high-level builder pattern**:
- `VulkanDevice::new(window_handle)` - Auto-selects GPU, creates device
- `Swapchain::new(device, width, height)` - Smart defaults, triple buffering
- `RenderPass::new(device, swapchain)` - Infers configuration from swapchain

### Implemented FFI Design

The Rust FFI uses a **low-level handle-based approach**:
- Explicit handle creation: `rt_vk_device_create()` → device_handle
- Explicit configuration: `rt_vk_swapchain_create(device, surface, width, height, hdr, vsync)`
- Manual resource management: `rt_vk_*_destroy(handle)`

### Gap Analysis

**Mismatch:** Simple API expects window handles as input, but window creation is blocked.

**Solutions:**
1. **Option A:** Update Simple API to match implemented FFI (low-level)
2. **Option B:** Add high-level wrapper layer in Simple stdlib (recommended)
3. **Option C:** Implement high-level FFI functions matching Simple API

**Recommendation:** Option B - Keep low-level FFI, build high-level Simple wrappers

**Example:**
```simple
# High-level Simple wrapper (in stdlib)
pub fn create_vulkan_device(window_handle: i64) -> Result[VulkanDevice, String]:
    # Create device via low-level FFI
    let device_handle = rt_vk_device_create()

    # Query properties
    let properties = rt_vk_device_get_properties(device_handle)

    return Ok(VulkanDevice {
        handle: device_handle,
        properties: properties
    })
```

---

## Next Steps

### Immediate Actions

1. **Prioritize Event Loop Fix**
   - Unblocks all window operations
   - Required for any visual testing
   - 2-3 day effort

2. **Add Graphics Pipeline FFI**
   - Implementation exists, just needs FFI wrappers
   - 1 day effort
   - Enables shader loading

3. **Update Simple stdlib API**
   - Align with implemented FFI design
   - Add high-level wrapper layer
   - Document FFI calling conventions

### Documentation Needed

1. **FFI Calling Conventions**
   - Error code mappings
   - Handle lifecycle management
   - Thread safety guarantees

2. **Simple API Guide**
   - Basic rendering tutorial
   - Async rendering patterns
   - Resource management best practices

3. **Example Programs**
   - Minimal triangle
   - Multi-window demo
   - HDR rendering

---

## Conclusion

The Vulkan graphics implementation provides **19 fully functional FFI functions** covering device creation, windows, swapchains, synchronization, presentation, and event handling. The core infrastructure is complete and well-tested (91 unit tests), with **19 FFI wrapper functions** remaining for full Simple language API support.

**Critical Path:**
1. ✅ Event loop refactoring - **COMPLETE** (unblocked window operations)
2. Graphics pipeline FFI (enables shader loading)
3. Render pass + framebuffer FFI (enables rendering)
4. Descriptor set FFI (enables uniforms/textures)

**Estimated effort:** 3-4 days for remaining critical path, 6-7 days for full API coverage

**Current Status:** Window creation and event handling fully functional, ready for Simple stdlib wrapper layer
