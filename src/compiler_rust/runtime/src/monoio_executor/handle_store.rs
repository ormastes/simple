// I/O Handle Storage with stable IDs
// Provides a generic storage mechanism for I/O handles with stable identifiers.

#![cfg(feature = "monoio-direct")]

use std::collections::HashMap;

/// Stores I/O handles with stable IDs that don't change
pub struct HandleStore<T> {
    next_id: i64,
    handles: HashMap<i64, Option<T>>,
}

impl<T> HandleStore<T> {
    pub fn new() -> Self {
        Self {
            next_id: 1,
            handles: HashMap::new(),
        }
    }

    /// Insert a handle and return its stable ID
    pub fn insert(&mut self, handle: T) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        self.handles.insert(id, Some(handle));
        id
    }

    /// Get a reference to a handle
    pub fn get(&self, id: i64) -> Option<&T> {
        self.handles.get(&id).and_then(|h| h.as_ref())
    }

    /// Get a mutable reference to a handle
    pub fn get_mut(&mut self, id: i64) -> Option<&mut T> {
        self.handles.get_mut(&id).and_then(|h| h.as_mut())
    }

    /// Take a handle temporarily (for async operations)
    pub fn take(&mut self, id: i64) -> Option<T> {
        self.handles.get_mut(&id).and_then(|h| h.take())
    }

    /// Return a handle after async operation
    pub fn put_back(&mut self, id: i64, handle: T) {
        if let Some(slot) = self.handles.get_mut(&id) {
            *slot = Some(handle);
        }
    }

    /// Remove a handle permanently
    pub fn remove(&mut self, id: i64) -> Option<T> {
        self.handles.remove(&id).flatten()
    }

    /// Check if a handle exists and is available
    pub fn is_available(&self, id: i64) -> bool {
        self.handles.get(&id).map(|h| h.is_some()).unwrap_or(false)
    }

    /// Count of active handles
    pub fn len(&self) -> usize {
        self.handles.values().filter(|h| h.is_some()).count()
    }

    /// Check if store is empty
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Default for HandleStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_store() {
        let mut store: HandleStore<i32> = HandleStore::new();

        let id1 = store.insert(100);
        let id2 = store.insert(200);

        assert_eq!(id1, 1);
        assert_eq!(id2, 2);
        assert_eq!(store.get(id1), Some(&100));
        assert_eq!(store.get(id2), Some(&200));

        // Take and put back
        let val = store.take(id1);
        assert_eq!(val, Some(100));
        assert!(!store.is_available(id1));

        store.put_back(id1, 150);
        assert!(store.is_available(id1));
        assert_eq!(store.get(id1), Some(&150));

        // Remove
        store.remove(id2);
        assert!(!store.is_available(id2));
    }

    #[test]
    fn test_handle_store_len() {
        let mut store: HandleStore<String> = HandleStore::new();
        assert_eq!(store.len(), 0);

        store.insert("test".to_string());
        assert_eq!(store.len(), 1);
    }
}
