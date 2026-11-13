//! `vkCreateDevice` bounded retry and init-error text, shared by every Rust
//! lane that creates a Vulkan device: the compiled runtime
//! (`vulkan/device.rs`, ash) and the seed interpreter's dlopen bridge
//! (`simple-compiler`, `interpreter_extern/gpu.rs`). Not feature-gated: the
//! interpreter lane builds without the `vulkan` cargo feature.
//!
//! See doc/08_tracking/bug/vulkan_runtime_init_nvidia_create_device_contention_2026-11-13.md.

/// Waits between `vkCreateDevice` attempts, in ms. Bounded: 5 attempts, 750 ms.
pub const VK_CREATE_DEVICE_RETRY_DELAYS_MS: [u64; 4] = [50, 100, 200, 400];

const VK_ERROR_INITIALIZATION_FAILED: i32 = -3;

pub fn vk_result_name(r: i32) -> &'static str {
    match r {
        0 => "VK_SUCCESS",
        -1 => "VK_ERROR_OUT_OF_HOST_MEMORY",
        -2 => "VK_ERROR_OUT_OF_DEVICE_MEMORY",
        -3 => "VK_ERROR_INITIALIZATION_FAILED",
        -4 => "VK_ERROR_DEVICE_LOST",
        -6 => "VK_ERROR_LAYER_NOT_PRESENT",
        -7 => "VK_ERROR_EXTENSION_NOT_PRESENT",
        -8 => "VK_ERROR_FEATURE_NOT_PRESENT",
        -9 => "VK_ERROR_INCOMPATIBLE_DRIVER",
        -10 => "VK_ERROR_TOO_MANY_OBJECTS",
        5 => "VK_INCOMPLETE",
        _ => "VkResult",
    }
}

/// The one error text for a failed `vkCreateDevice`, e.g.
/// `vkCreateDevice(device 0 of 2, queue family 0, 5 attempt(s)): VK_ERROR_INITIALIZATION_FAILED (-3)`.
pub fn vk_create_device_error(device_index: usize, device_count: usize, queue_family: u32, attempts: u32, r: i32) -> String {
    format!(
        "vkCreateDevice(device {device_index} of {device_count}, queue family {queue_family}, {attempts} attempt(s)): {} ({r})",
        vk_result_name(r)
    )
}

/// The production `sleep_ms` argument of [`vk_create_device_with_retry`].
pub fn vk_retry_sleep_ms(ms: u64) {
    std::thread::sleep(std::time::Duration::from_millis(ms));
}

/// `vkCreateDevice` with a bounded retry on `VK_ERROR_INITIALIZATION_FAILED`.
///
/// The NVIDIA driver returns that code transiently while other processes are
/// creating devices on the same GPU. Only that one code is retried, every
/// failed attempt is logged, and an exhausted retry still returns the error —
/// the caller fails closed. The success path makes one call and never sleeps.
/// `create` returns `Err(raw VkResult)`. Returns (result, attempts).
pub fn vk_create_device_with_retry<T>(
    mut create: impl FnMut() -> Result<T, i32>,
    mut sleep_ms: impl FnMut(u64),
) -> (Result<T, i32>, u32) {
    // RED: single attempt, no retry.
    let _ = &mut sleep_ms;
    (create(), 1)
}

#[cfg(test)]
mod vk_create_device_retry_tests {
    use super::*;

    const INIT_FAILED: i32 = -3;

    fn stub(calls: &mut u32, fail_first: u32, code: i32) -> Result<u32, i32> {
        *calls += 1;
        if *calls <= fail_first {
            Err(code)
        } else {
            Ok(*calls)
        }
    }

    #[test]
    fn success_makes_one_call_and_never_sleeps() {
        let mut calls = 0;
        let mut slept = Vec::new();
        let (r, attempts) = vk_create_device_with_retry(|| stub(&mut calls, 0, INIT_FAILED), |ms| slept.push(ms));
        assert_eq!((r, attempts, calls), (Ok(1), 1, 1));
        assert!(slept.is_empty());
    }

    #[test]
    fn transient_initialization_failed_recovers() {
        let mut calls = 0;
        let mut slept = Vec::new();
        let (r, attempts) = vk_create_device_with_retry(|| stub(&mut calls, 2, INIT_FAILED), |ms| slept.push(ms));
        assert_eq!((r, attempts), (Ok(3), 3));
        assert_eq!(slept, VK_CREATE_DEVICE_RETRY_DELAYS_MS[..2].to_vec());
    }

    #[test]
    fn persistent_initialization_failed_stays_failed_and_is_bounded() {
        let mut calls = 0;
        let mut slept = Vec::new();
        let (r, attempts) =
            vk_create_device_with_retry(|| stub(&mut calls, u32::MAX, INIT_FAILED), |ms| slept.push(ms));
        let max = VK_CREATE_DEVICE_RETRY_DELAYS_MS.len() as u32 + 1;
        assert_eq!((r, attempts, calls), (Err(INIT_FAILED), max, max));
        assert_eq!(slept, VK_CREATE_DEVICE_RETRY_DELAYS_MS.to_vec());
    }

    #[test]
    fn other_errors_are_not_retried() {
        for code in [-1, -2, -4, -7, -8, -10] {
            let mut calls = 0;
            let mut slept = Vec::new();
            let (r, attempts) = vk_create_device_with_retry(|| stub(&mut calls, u32::MAX, code), |ms| slept.push(ms));
            assert_eq!((r, attempts, calls), (Err(code), 1, 1));
            assert!(slept.is_empty());
        }
    }

    #[test]
    fn error_text_matches_the_interpreter_lane() {
        assert_eq!(
            vk_create_device_error(0, 2, 0, 5, INIT_FAILED),
            "vkCreateDevice(device 0 of 2, queue family 0, 5 attempt(s)): VK_ERROR_INITIALIZATION_FAILED (-3)"
        );
    }
}
