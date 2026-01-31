//! Dataset loaders for common ML datasets
//!
//! Provides MNIST and CIFAR-10 dataset download and loading functionality.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::storage::store_tensor;

// Macro to reduce feature flag duplication
macro_rules! pytorch_fn {
    ($name:ident, $params:tt, $ret:ty, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> $ret $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> $ret {
            Default::default()
        }
    };
    ($name:ident, $params:tt, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue {
            RuntimeValue::NIL
        }
    };
}

// ============================================================================
// Dataset Storage
// ============================================================================

/// Dataset handle
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct DatasetHandle {
    images: i64, // Tensor handle for images
    labels: i64, // Tensor handle for labels
    size: i64,   // Number of samples
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref DATASET_MAP: Mutex<HashMap<i64, DatasetHandle>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static DATASET_COUNTER: AtomicI64 = AtomicI64::new(1);

// ============================================================================
// MNIST Operations
// ============================================================================

pytorch_fn!(rt_torch_mnist_download, (path_ptr: *const u8, path_len: u64), i64, {
    if path_ptr.is_null() {
        return 0;
    }

    let path_slice = unsafe { std::slice::from_raw_parts(path_ptr, path_len as usize) };
    let path_str = match std::str::from_utf8(path_slice) {
        Ok(s) => s,
        Err(_) => return 0,
    };

    // Note: tch 0.18+ removed standalone download functions
    // The load_dir function will handle downloading if needed
    // For now, we check if the directory exists and return success
    // The actual download happens during load
    if std::path::Path::new(path_str).exists() || std::fs::create_dir_all(path_str).is_ok() {
        1
    } else {
        0
    }
});

pytorch_fn!(rt_torch_mnist_load, (path_ptr: *const u8, path_len: u64, train: i64), {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_slice = unsafe { std::slice::from_raw_parts(path_ptr, path_len as usize) };
    let path_str = match std::str::from_utf8(path_slice) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match tch::vision::mnist::load_dir(path_str) {
        Ok(dataset) => {
            let (images, labels) = if train != 0 {
                (dataset.train_images, dataset.train_labels)
            } else {
                (dataset.test_images, dataset.test_labels)
            };

            let size = images.size()[0];
            let images_handle = store_tensor(images);
            let labels_handle = store_tensor(labels);

            let ds = DatasetHandle {
                images: images_handle,
                labels: labels_handle,
                size,
            };

            let handle = DATASET_COUNTER.fetch_add(1, Ordering::SeqCst);
            DATASET_MAP.lock().unwrap().insert(handle, ds);
            RuntimeValue::from_int(handle)
        }
        Err(_) => RuntimeValue::NIL,
    }
});

// ============================================================================
// CIFAR-10 Operations
// ============================================================================

pytorch_fn!(rt_torch_cifar10_download, (path_ptr: *const u8, path_len: u64), i64, {
    if path_ptr.is_null() {
        return 0;
    }

    let path_slice = unsafe { std::slice::from_raw_parts(path_ptr, path_len as usize) };
    let path_str = match std::str::from_utf8(path_slice) {
        Ok(s) => s,
        Err(_) => return 0,
    };

    // Note: tch 0.18+ removed standalone download functions
    // The load_dir function will handle downloading if needed
    // For now, we check if the directory exists and return success
    if std::path::Path::new(path_str).exists() || std::fs::create_dir_all(path_str).is_ok() {
        1
    } else {
        0
    }
});

pytorch_fn!(rt_torch_cifar10_load, (path_ptr: *const u8, path_len: u64, train: i64), {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_slice = unsafe { std::slice::from_raw_parts(path_ptr, path_len as usize) };
    let path_str = match std::str::from_utf8(path_slice) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match tch::vision::cifar::load_dir(path_str) {
        Ok(dataset) => {
            let (images, labels) = if train != 0 {
                (dataset.train_images, dataset.train_labels)
            } else {
                (dataset.test_images, dataset.test_labels)
            };

            let size = images.size()[0];
            let images_handle = store_tensor(images);
            let labels_handle = store_tensor(labels);

            let ds = DatasetHandle {
                images: images_handle,
                labels: labels_handle,
                size,
            };

            let handle = DATASET_COUNTER.fetch_add(1, Ordering::SeqCst);
            DATASET_MAP.lock().unwrap().insert(handle, ds);
            RuntimeValue::from_int(handle)
        }
        Err(_) => RuntimeValue::NIL,
    }
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_mnist_download() {
        use super::*;
        use std::ptr;
        // Null path should return 0
        let result = rt_torch_mnist_download(ptr::null(), 0);
        assert_eq!(result, 0);
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_cifar10_download() {
        use super::*;
        use std::ptr;
        // Null path should return 0
        let result = rt_torch_cifar10_download(ptr::null(), 0);
        assert_eq!(result, 0);
    }
}
