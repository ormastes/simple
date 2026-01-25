//! FFI Type Registry for object-based FFI system.
//!
//! This module provides the central registry for FFI types, managing:
//! - Type registration and ID assignment
//! - Object storage with handle-based access
//! - Type metadata (vtables, names)
//!
//! # Architecture
//!
//! ```text
//! FfiTypeRegistry (global singleton)
//! ┌───────────────────────────────────────────────────────────────┐
//! │ types: HashMap<type_id, FfiTypeMetadata>                      │
//! │ name_to_id: HashMap<type_name, type_id>                       │
//! │ next_id: AtomicU32                                            │
//! └───────────────────────────────────────────────────────────────┘
//!       │
//!       ▼
//! FfiTypeMetadata (per registered type)
//! ┌───────────────────────────────────────────────────────────────┐
//! │ type_id: u32                                                  │
//! │ type_name: String                                             │
//! │ vtable: Box<FfiVtable>                                        │
//! │ storage: FfiObjectStorage                                     │
//! └───────────────────────────────────────────────────────────────┘
//!       │
//!       ▼
//! FfiObjectStorage
//! ┌───────────────────────────────────────────────────────────────┐
//! │ objects: HashMap<handle, Box<dyn Any + Send + Sync>>          │
//! │ next_handle: AtomicU32                                        │
//! └───────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Thread Safety
//!
//! The registry uses RwLock for concurrent read access with exclusive write access.
//! Object storage within each type uses a separate Mutex for fine-grained locking.

use std::any::Any;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, RwLock};

use super::core::RuntimeValue;
use super::ffi_object::{FfiVtable, RuntimeFfiObject};
use super::heap::HeapHeader;

// ============================================================================
// Global Registry Singleton
// ============================================================================

lazy_static::lazy_static! {
    /// Global FFI type registry.
    static ref FFI_TYPE_REGISTRY: FfiTypeRegistry = FfiTypeRegistry::new();
}

/// Get a reference to the global FFI type registry.
pub fn get_registry() -> &'static FfiTypeRegistry {
    &FFI_TYPE_REGISTRY
}

// ============================================================================
// Storage for FFI Objects
// ============================================================================

/// Thread-safe storage for FFI objects of a specific type.
///
/// Objects are stored as `Box<dyn Any + Send + Sync>` to allow heterogeneous
/// storage while maintaining type safety through downcasting.
pub struct FfiObjectStorage {
    /// Map from handle to boxed object.
    objects: Mutex<HashMap<u32, Box<dyn Any + Send + Sync>>>,
    /// Counter for generating unique handles.
    next_handle: AtomicU32,
}

impl FfiObjectStorage {
    /// Create a new empty storage.
    pub fn new() -> Self {
        Self {
            objects: Mutex::new(HashMap::new()),
            // Start at 1 so 0 can indicate "invalid handle"
            next_handle: AtomicU32::new(1),
        }
    }

    /// Insert an object and return its handle.
    pub fn insert<T: Any + Send + Sync>(&self, object: T) -> u32 {
        let handle = self.next_handle.fetch_add(1, Ordering::SeqCst);
        let mut objects = self.objects.lock().unwrap();
        objects.insert(handle, Box::new(object));
        handle
    }

    /// Get a reference to an object by handle.
    ///
    /// Returns None if the handle doesn't exist or the type doesn't match.
    pub fn get<T: Any + Send + Sync>(&self, handle: u32) -> Option<std::sync::MutexGuard<'_, HashMap<u32, Box<dyn Any + Send + Sync>>>> {
        let objects = self.objects.lock().unwrap();
        if objects.contains_key(&handle) {
            Some(objects)
        } else {
            None
        }
    }

    /// Execute a function with a reference to the object.
    ///
    /// This avoids lifetime issues by executing the closure while holding the lock.
    pub fn with<T: Any + Send + Sync, R, F: FnOnce(&T) -> R>(&self, handle: u32, f: F) -> Option<R> {
        let objects = self.objects.lock().unwrap();
        objects
            .get(&handle)
            .and_then(|obj| obj.downcast_ref::<T>())
            .map(f)
    }

    /// Execute a function with a mutable reference to the object.
    pub fn with_mut<T: Any + Send + Sync, R, F: FnOnce(&mut T) -> R>(&self, handle: u32, f: F) -> Option<R> {
        let mut objects = self.objects.lock().unwrap();
        objects
            .get_mut(&handle)
            .and_then(|obj| obj.downcast_mut::<T>())
            .map(f)
    }

    /// Remove an object by handle.
    ///
    /// Returns true if the object was removed, false if it didn't exist.
    pub fn remove(&self, handle: u32) -> bool {
        let mut objects = self.objects.lock().unwrap();
        objects.remove(&handle).is_some()
    }

    /// Check if a handle exists.
    pub fn contains(&self, handle: u32) -> bool {
        let objects = self.objects.lock().unwrap();
        objects.contains_key(&handle)
    }

    /// Get the number of stored objects.
    pub fn len(&self) -> usize {
        let objects = self.objects.lock().unwrap();
        objects.len()
    }

    /// Check if storage is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clear all stored objects.
    pub fn clear(&self) {
        let mut objects = self.objects.lock().unwrap();
        objects.clear();
    }
}

impl Default for FfiObjectStorage {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Type Metadata
// ============================================================================

/// Metadata for a registered FFI type.
pub struct FfiTypeMetadata {
    /// Unique type ID.
    pub type_id: u32,
    /// Type name (for debugging/reflection).
    pub type_name: String,
    /// Virtual table for method dispatch.
    /// This is a raw pointer because vtables are typically static.
    pub vtable: *const FfiVtable,
    /// Object storage for this type.
    pub storage: FfiObjectStorage,
}

impl FfiTypeMetadata {
    /// Create new type metadata.
    ///
    /// # Safety
    /// The vtable pointer must be valid for the lifetime of this metadata.
    pub fn new(type_id: u32, type_name: String, vtable: *const FfiVtable) -> Self {
        Self {
            type_id,
            type_name,
            vtable,
            storage: FfiObjectStorage::new(),
        }
    }
}

// Safety: FfiTypeMetadata is safe to send/sync because:
// - type_id and type_name are owned
// - vtable points to static data
// - storage uses internal synchronization
unsafe impl Send for FfiTypeMetadata {}
unsafe impl Sync for FfiTypeMetadata {}

// ============================================================================
// Type Registry
// ============================================================================

/// Central registry for FFI types.
///
/// This registry manages:
/// - Type registration and ID assignment
/// - Type metadata lookup
/// - Object creation and destruction
pub struct FfiTypeRegistry {
    /// Map from type ID to metadata.
    types: RwLock<HashMap<u32, FfiTypeMetadata>>,
    /// Map from type name to ID (for lookup by name).
    name_to_id: RwLock<HashMap<String, u32>>,
    /// Counter for generating unique type IDs.
    next_id: AtomicU32,
}

impl FfiTypeRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            types: RwLock::new(HashMap::new()),
            name_to_id: RwLock::new(HashMap::new()),
            // Start at 1 so 0 can indicate "unregistered type"
            next_id: AtomicU32::new(1),
        }
    }

    /// Register a new FFI type.
    ///
    /// # Parameters
    /// - `type_name`: Name of the type (must be unique)
    /// - `vtable`: Pointer to the type's vtable (must be static)
    ///
    /// # Returns
    /// The assigned type ID, or 0 if a type with that name already exists.
    pub fn register_type(&self, type_name: &str, vtable: *const FfiVtable) -> u32 {
        // Check if already registered
        {
            let name_to_id = self.name_to_id.read().unwrap();
            if name_to_id.contains_key(type_name) {
                return 0;
            }
        }

        // Allocate new type ID
        let type_id = self.next_id.fetch_add(1, Ordering::SeqCst);

        // Create metadata
        let metadata = FfiTypeMetadata::new(type_id, type_name.to_string(), vtable);

        // Insert into both maps
        {
            let mut types = self.types.write().unwrap();
            let mut name_to_id = self.name_to_id.write().unwrap();

            types.insert(type_id, metadata);
            name_to_id.insert(type_name.to_string(), type_id);
        }

        type_id
    }

    /// Get the type ID for a type name.
    ///
    /// Returns 0 if the type is not registered.
    pub fn get_type_id(&self, type_name: &str) -> u32 {
        let name_to_id = self.name_to_id.read().unwrap();
        name_to_id.get(type_name).copied().unwrap_or(0)
    }

    /// Get the type name for a type ID.
    ///
    /// Returns None if the type ID is not registered.
    pub fn get_type_name(&self, type_id: u32) -> Option<String> {
        let types = self.types.read().unwrap();
        types.get(&type_id).map(|m| m.type_name.clone())
    }

    /// Get the vtable for a type ID.
    ///
    /// Returns null if the type ID is not registered.
    pub fn get_vtable(&self, type_id: u32) -> *const FfiVtable {
        let types = self.types.read().unwrap();
        types.get(&type_id).map(|m| m.vtable).unwrap_or(std::ptr::null())
    }

    /// Create a new object of the given type.
    ///
    /// # Type Parameters
    /// - `T`: The Rust type to store
    ///
    /// # Parameters
    /// - `type_id`: The registered type ID
    /// - `object`: The object to store
    ///
    /// # Returns
    /// A RuntimeValue containing the FFI object, or NIL if the type is not registered.
    pub fn create_object<T: Any + Send + Sync>(&self, type_id: u32, object: T) -> RuntimeValue {
        let types = self.types.read().unwrap();
        let Some(metadata) = types.get(&type_id) else {
            return RuntimeValue::NIL;
        };

        // Store the object
        let handle = metadata.storage.insert(object);

        // Create the FFI object on the heap
        unsafe {
            super::ffi_object::rt_ffi_object_new(type_id, handle, metadata.vtable)
        }
    }

    /// Get a reference to an object's storage.
    ///
    /// This is useful for executing operations on the stored object.
    pub fn with_storage<R, F: FnOnce(&FfiObjectStorage) -> R>(&self, type_id: u32, f: F) -> Option<R> {
        let types = self.types.read().unwrap();
        types.get(&type_id).map(|m| f(&m.storage))
    }

    /// Drop an FFI object.
    ///
    /// This removes the object from storage and deallocates the heap memory.
    ///
    /// # Safety
    /// The value must be a valid FFI object.
    pub unsafe fn drop_object(&self, value: RuntimeValue) -> bool {
        if !value.is_heap() {
            return false;
        }

        let ptr = value.as_heap_ptr();
        if ptr.is_null() {
            return false;
        }

        if (*ptr).object_type != super::heap::HeapObjectType::FfiObject {
            return false;
        }

        let ffi_obj = &*(ptr as *const RuntimeFfiObject);
        let type_id = ffi_obj.type_id;
        let handle = ffi_obj.handle;

        // Call the drop function if one is registered
        if !ffi_obj.vtable.is_null() {
            if let Some(drop_fn) = (*ffi_obj.vtable).drop_fn {
                drop_fn(handle);
            }
        }

        // Remove from storage
        {
            let types = self.types.read().unwrap();
            if let Some(metadata) = types.get(&type_id) {
                metadata.storage.remove(handle);
            }
        }

        // Free the heap memory
        super::ffi_object::rt_ffi_object_free(value);

        true
    }

    /// Clone an FFI object.
    ///
    /// If the type supports cloning, creates a new object with a copy of the data.
    ///
    /// # Returns
    /// A new RuntimeValue containing the cloned object, or NIL if cloning is not supported.
    pub unsafe fn clone_object(&self, value: RuntimeValue) -> RuntimeValue {
        if !value.is_heap() {
            return RuntimeValue::NIL;
        }

        let ptr = value.as_heap_ptr();
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        if (*ptr).object_type != super::heap::HeapObjectType::FfiObject {
            return RuntimeValue::NIL;
        }

        let ffi_obj = &*(ptr as *const RuntimeFfiObject);

        // Check if clone is supported
        if ffi_obj.vtable.is_null() {
            return RuntimeValue::NIL;
        }

        let clone_fn = (*ffi_obj.vtable).clone_fn;
        let Some(clone_fn) = clone_fn else {
            return RuntimeValue::NIL;
        };

        // Call the clone function to get a new handle
        let new_handle = clone_fn(ffi_obj.handle);
        if new_handle == 0 {
            return RuntimeValue::NIL;
        }

        // Create a new FFI object with the new handle
        super::ffi_object::rt_ffi_object_new(ffi_obj.type_id, new_handle, ffi_obj.vtable)
    }

    /// Get the number of registered types.
    pub fn type_count(&self) -> usize {
        let types = self.types.read().unwrap();
        types.len()
    }

    /// Get the number of objects of a specific type.
    pub fn object_count(&self, type_id: u32) -> usize {
        let types = self.types.read().unwrap();
        types.get(&type_id).map(|m| m.storage.len()).unwrap_or(0)
    }

    /// Clear all objects of a specific type (for testing).
    pub fn clear_type(&self, type_id: u32) {
        let types = self.types.read().unwrap();
        if let Some(metadata) = types.get(&type_id) {
            metadata.storage.clear();
        }
    }

    /// Clear all registered types and objects (for testing).
    pub fn clear_all(&self) {
        let mut types = self.types.write().unwrap();
        let mut name_to_id = self.name_to_id.write().unwrap();

        types.clear();
        name_to_id.clear();
    }
}

impl Default for FfiTypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// FFI Functions for Type Registry
// ============================================================================

/// Register a new FFI type.
///
/// # Parameters
/// - `name_ptr`: Pointer to the type name (UTF-8, null-terminated)
/// - `name_len`: Length of the type name
/// - `vtable`: Pointer to the type's vtable
///
/// # Returns
/// The assigned type ID, or 0 if registration fails.
#[no_mangle]
pub extern "C" fn rt_ffi_type_register(
    name_ptr: *const u8,
    name_len: u32,
    vtable: *const FfiVtable,
) -> u32 {
    if name_ptr.is_null() || vtable.is_null() {
        return 0;
    }

    let name = unsafe {
        let bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
        match std::str::from_utf8(bytes) {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };

    get_registry().register_type(name, vtable)
}

/// Get the type ID for a type name.
///
/// # Returns
/// The type ID, or 0 if the type is not registered.
#[no_mangle]
pub extern "C" fn rt_ffi_type_id(name_ptr: *const u8, name_len: u32) -> u32 {
    if name_ptr.is_null() {
        return 0;
    }

    let name = unsafe {
        let bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
        match std::str::from_utf8(bytes) {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };

    get_registry().get_type_id(name)
}

/// Get the type name for a type ID.
///
/// # Returns
/// A RuntimeValue containing the type name string, or NIL if not found.
#[no_mangle]
pub extern "C" fn rt_ffi_type_name(type_id: u32) -> RuntimeValue {
    let Some(name) = get_registry().get_type_name(type_id) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        super::collections::rt_string_new(name.as_ptr(), name.len() as u64)
    }
}

/// Create a new FFI object.
///
/// This is a low-level function that creates the heap representation only.
/// The actual object should be stored separately (e.g., in a type-specific registry).
///
/// # Parameters
/// - `type_id`: The registered type ID
/// - `handle`: Handle to the object in type-specific storage
///
/// # Returns
/// A RuntimeValue containing the FFI object, or NIL if the type is not registered.
#[no_mangle]
pub extern "C" fn rt_ffi_new(type_id: u32, handle: u32) -> RuntimeValue {
    let vtable = get_registry().get_vtable(type_id);
    if vtable.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe { super::ffi_object::rt_ffi_object_new(type_id, handle, vtable) }
}

/// Drop an FFI object.
///
/// This removes the object from storage, calls the drop function, and frees memory.
///
/// # Returns
/// `true` if the object was dropped, `false` otherwise.
#[no_mangle]
pub extern "C" fn rt_ffi_drop(value: RuntimeValue) -> bool {
    unsafe { get_registry().drop_object(value) }
}

/// Clone an FFI object.
///
/// # Returns
/// A new RuntimeValue containing the cloned object, or NIL if cloning fails.
#[no_mangle]
pub extern "C" fn rt_ffi_clone(value: RuntimeValue) -> RuntimeValue {
    unsafe { get_registry().clone_object(value) }
}

/// Check if a value is an FFI object of a specific type.
#[no_mangle]
pub extern "C" fn rt_ffi_is_type(value: RuntimeValue, type_id: u32) -> bool {
    super::ffi_object::rt_ffi_object_type_id(value) == type_id
}

/// Call a method on an FFI object.
///
/// # Parameters
/// - `value`: The FFI object
/// - `name_ptr`: Pointer to the method name (UTF-8)
/// - `name_len`: Length of the method name
/// - `argc`: Number of arguments
/// - `argv`: Pointer to the argument array
///
/// # Returns
/// The result of the method call, or NIL if the method doesn't exist.
#[no_mangle]
pub unsafe extern "C" fn rt_ffi_call_method(
    value: RuntimeValue,
    name_ptr: *const u8,
    name_len: u32,
    argc: u32,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    super::ffi_object::rt_ffi_object_call_method(value, name_ptr, name_len, argc, argv)
}

/// Check if an FFI object has a specific method.
#[no_mangle]
pub extern "C" fn rt_ffi_has_method(value: RuntimeValue, name_ptr: *const u8, name_len: u32) -> bool {
    super::ffi_object::rt_ffi_object_has_method(value, name_ptr, name_len)
}

/// Clear the FFI type registry (for testing).
#[no_mangle]
pub extern "C" fn rt_ffi_clear_registry() {
    get_registry().clear_all();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::ffi_object::{FfiMethodEntry, fnv1a_hash_str};

    // Create a test vtable
    static TEST_TYPE_NAME: &[u8] = b"TestType";
    static TEST_METHODS: [FfiMethodEntry; 0] = [];
    static TEST_VTABLE: FfiVtable = FfiVtable {
        type_name: TEST_TYPE_NAME.as_ptr(),
        type_name_len: 8,
        method_count: 0,
        methods: TEST_METHODS.as_ptr(),
        drop_fn: None,
        clone_fn: None,
    };

    #[test]
    fn test_type_registration() {
        let registry = FfiTypeRegistry::new();

        // Register a type
        let type_id = registry.register_type("TestType", &TEST_VTABLE);
        assert_ne!(type_id, 0);

        // Look up by name
        assert_eq!(registry.get_type_id("TestType"), type_id);
        assert_eq!(registry.get_type_id("Unknown"), 0);

        // Look up by ID
        assert_eq!(registry.get_type_name(type_id), Some("TestType".to_string()));
        assert_eq!(registry.get_type_name(999), None);

        // Duplicate registration should fail
        let dup_id = registry.register_type("TestType", &TEST_VTABLE);
        assert_eq!(dup_id, 0);
    }

    #[test]
    fn test_object_storage() {
        let storage = FfiObjectStorage::new();

        // Insert some objects
        let h1 = storage.insert(42i32);
        let h2 = storage.insert("hello".to_string());
        let h3 = storage.insert(vec![1, 2, 3]);

        // Verify handles are unique
        assert_ne!(h1, h2);
        assert_ne!(h2, h3);
        assert_ne!(h1, h3);

        // Access objects
        let result = storage.with::<i32, _, _>(h1, |v| *v);
        assert_eq!(result, Some(42));

        let result = storage.with::<String, _, _>(h2, |v| v.clone());
        assert_eq!(result, Some("hello".to_string()));

        // Wrong type should return None
        let result = storage.with::<String, _, _>(h1, |v| v.clone());
        assert_eq!(result, None);

        // Mutate an object
        storage.with_mut::<i32, _, _>(h1, |v| *v = 100);
        let result = storage.with::<i32, _, _>(h1, |v| *v);
        assert_eq!(result, Some(100));

        // Remove an object
        assert!(storage.remove(h1));
        assert!(!storage.contains(h1));
        assert!(storage.contains(h2));

        // Remove non-existent handle
        assert!(!storage.remove(h1));
    }

    #[test]
    fn test_storage_clear() {
        let storage = FfiObjectStorage::new();

        storage.insert(1i32);
        storage.insert(2i32);
        storage.insert(3i32);

        assert_eq!(storage.len(), 3);

        storage.clear();

        assert_eq!(storage.len(), 0);
        assert!(storage.is_empty());
    }
}
