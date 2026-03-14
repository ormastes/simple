# Vulkan FFI Swapchain Module - Quick Reference

## Module Hierarchy

```
simple/
└── src/
    └── runtime/
        └── src/
            └── value/
                ├── gpu_vulkan.rs                    (Original source, functions now extracted)
                └── vulkan_ffi/
                    ├── mod.rs                       (Module registry, re-exports)
                    ├── common.rs                    (Shared registries, error types)
                    ├── device.rs                    (Device management)
                    ├── buffer.rs                    (Buffer management)
                    ├── kernel.rs                    (Compute kernel management)
                    ├── descriptor.rs                (Descriptor set management)
                    ├── swapchain.rs                 (NEW: Swapchain management)
                    └── window.rs                    (Window management)
```

## Swapchain Module Contents

### File Path
`/home/ormastes/dev/pub/simple/src/runtime/src/value/vulkan_ffi/swapchain.rs`

### Size
- **317 lines** total
- **~100 lines** documentation
- **~217 lines** implementation
- **7 functions**

### Public API Functions

#### Creation & Lifecycle
```rust
pub extern "C" fn rt_vk_swapchain_create(
    device_handle: u64,
    surface_handle: u64,
    width: u32,
    height: u32,
    prefer_hdr: i32,
    prefer_no_vsync: i32,
) -> i64;

pub extern "C" fn rt_vk_swapchain_recreate(
    swapchain_handle: u64,
    surface_handle: u64,
    width: u32,
    height: u32,
) -> i32;

pub extern "C" fn rt_vk_swapchain_destroy(swapchain_handle: u64) -> i32;
```

#### Image Acquisition & Presentation
```rust
pub extern "C" fn rt_vk_swapchain_acquire_next_image(
    swapchain_handle: u64,
    timeout_ns: u64,
    out_suboptimal: *mut i32,
) -> i32;

pub extern "C" fn rt_vk_swapchain_present(
    swapchain_handle: u64,
    image_index: u32,
) -> i32;
```

#### Query Operations
```rust
pub extern "C" fn rt_vk_swapchain_get_image_count(swapchain_handle: u64) -> i32;

pub extern "C" fn rt_vk_swapchain_get_extent(
    swapchain_handle: u64,
    out_width: *mut u32,
    out_height: *mut u32,
) -> i32;
```

## Module Integration

### In `vulkan_ffi/mod.rs`

**Module Declaration** (line 20):
```rust
pub mod swapchain;
```

**Documentation** (line 12):
```
- `swapchain`: Swapchain management (create, recreate, acquire, present)
```

**Re-exports** (lines 36-41):
```rust
pub use swapchain::{
    rt_vk_swapchain_create, rt_vk_swapchain_recreate, rt_vk_swapchain_destroy,
    rt_vk_swapchain_acquire_next_image, rt_vk_swapchain_present,
    rt_vk_swapchain_get_image_count, rt_vk_swapchain_get_extent,
};
```

## Imports and Dependencies

### From `super::common`
- `next_handle()` - Global handle generator
- `VulkanFfiError` - FFI error type with conversion impl
- `DEVICE_REGISTRY` - Device handle → VulkanDevice mapping
- `WINDOW_SURFACES` - Surface handle → Surface mapping
- `SWAPCHAIN_REGISTRY` - Swapchain handle → Arc<Mutex<VulkanSwapchain>> mapping

### From `crate::vulkan`
- `VulkanError` - Native Vulkan error type
- `VulkanSwapchain` - Swapchain implementation struct

### Standard Library
- `std::sync::Arc` - Shared ownership pointer
- `parking_lot::Mutex` - Interior mutability for thread-safe state

## Error Handling

All functions use the `VulkanFfiError` enum:
- `VulkanFfiError::Success = 0`
- `VulkanFfiError::NotAvailable = -1`
- `VulkanFfiError::InvalidHandle = -2`
- `VulkanFfiError::AllocationFailed = -3`
- `VulkanFfiError::SurfaceError = -9`
- `VulkanFfiError::InvalidParameter = -7`

Conversion from `VulkanError` is automatic via `From<VulkanError>` impl.

## Return Value Conventions

| Function | Success | Error | Special |
|----------|---------|-------|---------|
| `create` | handle (i64) | negative error | N/A |
| `recreate` | 0 | negative error | N/A |
| `destroy` | 0 | negative error | N/A |
| `acquire_next_image` | image index (i32) | negative error | suboptimal via *out_suboptimal |
| `present` | 0 | negative error | 1 = needs recreation |
| `get_image_count` | count (i32) | negative error | N/A |
| `get_extent` | 0 | negative error | w,h via *out_width/*out_height |

## Feature Compilation

All functions are guarded with `#[cfg(feature = "vulkan")]`:
- When feature is enabled: Full Vulkan implementation
- When feature is disabled: Returns `VulkanFfiError::NotAvailable`

## FFI Safety

### Unsafe Blocks
Used only for necessary FFI operations:
1. Writing to output pointers in acquire_next_image:
   ```rust
   unsafe { *out_suboptimal = ... }
   ```
2. Writing to extent pointers in get_extent:
   ```rust
   unsafe {
       *out_width = ...;
       *out_height = ...;
   }
   ```

### Validation
- All output pointers are null-checked before use
- Handles are validated via registry lookup
- Error conversion is automatic and safe

## Testing

The extracted functions preserve the same behavior as the original implementation.
Original tests from `gpu_vulkan.rs` can be integrated with these functions via:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires Vulkan
    fn test_swapchain_lifecycle() {
        // Create → recreate → destroy
    }
}
```

## Usage Example (FFI Perspective)

```rust
// Create device and surface (not shown)
let device_handle = rt_vk_device_create();
let surface_handle = rt_vk_window_create(...);

// Create swapchain
let swapchain = rt_vk_swapchain_create(
    device_handle,
    surface_handle,
    1920,
    1080,
    0,      // prefer_hdr = false
    0,      // prefer_no_vsync = false
);

if swapchain > 0 {
    // Rendering loop
    let mut suboptimal = 0;
    let image_idx = rt_vk_swapchain_acquire_next_image(
        swapchain,
        1_000_000_000,  // 1 second timeout
        &mut suboptimal,
    );

    if image_idx >= 0 {
        // Render to image...

        let needs_recreation = rt_vk_swapchain_present(swapchain, image_idx as u32);
        if needs_recreation == 1 {
            rt_vk_swapchain_recreate(swapchain, surface_handle, 1920, 1080);
        }
    }

    // Cleanup
    rt_vk_swapchain_destroy(swapchain);
}
```

## Compilation & Verification

✅ **Compilation**: Verified with `cargo check -p simple-runtime`
✅ **Formatting**: Verified with `rustfmt`
✅ **Module Visibility**: Public re-exports in `mod.rs`
✅ **Documentation**: Complete doc comments on all functions
✅ **Error Handling**: Proper FFI error conversion

## Related Modules

- **device.rs**: Device creation and management
- **buffer.rs**: GPU buffer allocation and transfers
- **kernel.rs**: Compute kernel compilation and execution
- **descriptor.rs**: Descriptor set and layout management
- **window.rs**: Window creation and event handling
- **common.rs**: Shared registries and error types
