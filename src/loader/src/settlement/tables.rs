//! Indirection tables for settlement.
//!
//! These tables enable hot-reload by providing a level of indirection
//! for function calls and global access.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use crate::smf::settlement::{
    FuncTableEntry, GlobalTableEntry, TypeTableEntry,
    FUNC_FLAG_TOMBSTONE, FUNC_FLAG_VALID,
};

/// A handle to an entry in an indirection table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TableIndex(pub u32);

impl TableIndex {
    pub const INVALID: TableIndex = TableIndex(u32::MAX);

    pub fn is_valid(&self) -> bool {
        self.0 != u32::MAX
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

/// Generic indirection table with free list management.
pub struct IndirectionTable<T: Default + Clone> {
    entries: Vec<T>,
    free_list: Vec<usize>,
}

impl<T: Default + Clone> IndirectionTable<T> {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            free_list: Vec::new(),
        }
    }

    /// Create a table with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
            free_list: Vec::new(),
        }
    }

    /// Get the number of entries (including tombstones).
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get number of active entries.
    pub fn active_count(&self) -> usize {
        self.entries.len() - self.free_list.len()
    }

    /// Allocate a new entry, returning its index.
    pub fn allocate(&mut self) -> TableIndex {
        if let Some(idx) = self.free_list.pop() {
            TableIndex(idx as u32)
        } else {
            let idx = self.entries.len();
            self.entries.push(T::default());
            TableIndex(idx as u32)
        }
    }

    /// Free an entry, adding it to the free list.
    pub fn free(&mut self, idx: TableIndex) {
        if idx.is_valid() && (idx.as_usize()) < self.entries.len() {
            self.entries[idx.as_usize()] = T::default();
            self.free_list.push(idx.as_usize());
        }
    }

    /// Get a reference to an entry.
    pub fn get(&self, idx: TableIndex) -> Option<&T> {
        if idx.is_valid() {
            self.entries.get(idx.as_usize())
        } else {
            None
        }
    }

    /// Get a mutable reference to an entry.
    pub fn get_mut(&mut self, idx: TableIndex) -> Option<&mut T> {
        if idx.is_valid() {
            self.entries.get_mut(idx.as_usize())
        } else {
            None
        }
    }

    /// Set an entry's value.
    pub fn set(&mut self, idx: TableIndex, value: T) {
        if idx.is_valid() && (idx.as_usize()) < self.entries.len() {
            self.entries[idx.as_usize()] = value;
        }
    }

    /// Iterate over all entries with their indices.
    pub fn iter(&self) -> impl Iterator<Item = (TableIndex, &T)> {
        self.entries
            .iter()
            .enumerate()
            .map(|(i, e)| (TableIndex(i as u32), e))
    }

    /// Get raw slice of entries (for serialization).
    pub fn as_slice(&self) -> &[T] {
        &self.entries
    }

    /// Get raw pointer to entries (for runtime use).
    pub fn as_ptr(&self) -> *const T {
        self.entries.as_ptr()
    }
}

impl<T: Default + Clone> Default for IndirectionTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Function table with atomic pointer updates for hot reload.
pub struct FunctionTable {
    inner: IndirectionTable<FuncTableEntry>,
}

impl FunctionTable {
    pub fn new() -> Self {
        Self {
            inner: IndirectionTable::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: IndirectionTable::with_capacity(capacity),
        }
    }

    /// Allocate a new function entry.
    pub fn allocate(&mut self, code_ptr: usize, module_id: u16, version: u16) -> TableIndex {
        let idx = self.inner.allocate();
        if let Some(entry) = self.inner.get_mut(idx) {
            entry.code_ptr = code_ptr as u64;
            entry.module_id = module_id;
            entry.version = version;
            entry.flags = FUNC_FLAG_VALID;
        }
        idx
    }

    /// Mark a function as tombstone (removed but slot not reused yet).
    pub fn mark_tombstone(&mut self, idx: TableIndex) {
        if let Some(entry) = self.inner.get_mut(idx) {
            entry.flags = FUNC_FLAG_TOMBSTONE;
            entry.code_ptr = 0;
        }
    }

    /// Free a function entry for reuse.
    pub fn free(&mut self, idx: TableIndex) {
        self.inner.free(idx);
    }

    /// Get function pointer.
    pub fn get_code_ptr(&self, idx: TableIndex) -> Option<usize> {
        self.inner.get(idx).and_then(|e| {
            if e.flags & FUNC_FLAG_VALID != 0 {
                Some(e.code_ptr as usize)
            } else {
                None
            }
        })
    }

    /// Update function pointer atomically (for hot reload).
    ///
    /// # Safety
    /// The caller must ensure the new code pointer is valid.
    pub unsafe fn update_code_ptr(&self, idx: TableIndex, new_ptr: usize) {
        if let Some(entry) = self.inner.get(idx) {
            // Cast to atomic and store
            let atomic = &entry.code_ptr as *const u64 as *const AtomicU64;
            (*atomic).store(new_ptr as u64, Ordering::Release);
        }
    }

    /// Get entry details.
    pub fn get_entry(&self, idx: TableIndex) -> Option<&FuncTableEntry> {
        self.inner.get(idx)
    }

    /// Get number of entries.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Get raw slice for serialization.
    pub fn as_slice(&self) -> &[FuncTableEntry] {
        self.inner.as_slice()
    }

    /// Iterate over valid entries.
    pub fn iter_valid(&self) -> impl Iterator<Item = (TableIndex, &FuncTableEntry)> {
        self.inner.iter().filter(|(_, e)| e.is_valid())
    }
}

impl Default for FunctionTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Global variable table.
pub struct GlobalTable {
    inner: IndirectionTable<GlobalTableEntry>,
}

impl GlobalTable {
    pub fn new() -> Self {
        Self {
            inner: IndirectionTable::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: IndirectionTable::with_capacity(capacity),
        }
    }

    /// Allocate a new global entry.
    pub fn allocate(&mut self, data_ptr: usize, size: u32, module_id: u16) -> TableIndex {
        let idx = self.inner.allocate();
        if let Some(entry) = self.inner.get_mut(idx) {
            entry.data_ptr = data_ptr as u64;
            entry.size = size;
            entry.module_id = module_id;
            entry.flags = 1; // Valid
        }
        idx
    }

    /// Free a global entry.
    pub fn free(&mut self, idx: TableIndex) {
        self.inner.free(idx);
    }

    /// Get global data pointer.
    pub fn get_data_ptr(&self, idx: TableIndex) -> Option<usize> {
        self.inner.get(idx).map(|e| e.data_ptr as usize)
    }

    /// Update global pointer atomically.
    ///
    /// # Safety
    /// The caller must ensure the new pointer is valid.
    pub unsafe fn update_data_ptr(&self, idx: TableIndex, new_ptr: usize) {
        if let Some(entry) = self.inner.get(idx) {
            let atomic = &entry.data_ptr as *const u64 as *const AtomicU64;
            (*atomic).store(new_ptr as u64, Ordering::Release);
        }
    }

    /// Get entry details.
    pub fn get_entry(&self, idx: TableIndex) -> Option<&GlobalTableEntry> {
        self.inner.get(idx)
    }

    /// Get number of entries.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Get raw slice for serialization.
    pub fn as_slice(&self) -> &[GlobalTableEntry] {
        self.inner.as_slice()
    }
}

impl Default for GlobalTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Type info table.
pub struct TypeTable {
    inner: IndirectionTable<TypeTableEntry>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            inner: IndirectionTable::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: IndirectionTable::with_capacity(capacity),
        }
    }

    /// Allocate a new type entry.
    pub fn allocate(&mut self, type_ptr: usize, layout_hash: u32, module_id: u16) -> TableIndex {
        let idx = self.inner.allocate();
        if let Some(entry) = self.inner.get_mut(idx) {
            entry.type_ptr = type_ptr as u64;
            entry.layout_hash = layout_hash;
            entry.module_id = module_id;
            entry.flags = 1; // Valid
        }
        idx
    }

    /// Free a type entry.
    pub fn free(&mut self, idx: TableIndex) {
        self.inner.free(idx);
    }

    /// Get type pointer.
    pub fn get_type_ptr(&self, idx: TableIndex) -> Option<usize> {
        self.inner.get(idx).map(|e| e.type_ptr as usize)
    }

    /// Get layout hash for compatibility checking.
    pub fn get_layout_hash(&self, idx: TableIndex) -> Option<u32> {
        self.inner.get(idx).map(|e| e.layout_hash)
    }

    /// Get entry details.
    pub fn get_entry(&self, idx: TableIndex) -> Option<&TypeTableEntry> {
        self.inner.get(idx)
    }

    /// Get number of entries.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Get raw slice for serialization.
    pub fn as_slice(&self) -> &[TypeTableEntry] {
        self.inner.as_slice()
    }
}

impl Default for TypeTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_table_index() {
        let idx = TableIndex(5);
        assert!(idx.is_valid());
        assert_eq!(idx.as_usize(), 5);

        assert!(!TableIndex::INVALID.is_valid());
    }

    #[test]
    fn test_indirection_table() {
        let mut table: IndirectionTable<u64> = IndirectionTable::new();

        let idx1 = table.allocate();
        table.set(idx1, 42);
        assert_eq!(*table.get(idx1).unwrap(), 42);

        let idx2 = table.allocate();
        table.set(idx2, 100);
        assert_eq!(table.len(), 2);

        table.free(idx1);
        assert_eq!(table.active_count(), 1);

        // Reuse freed slot
        let idx3 = table.allocate();
        assert_eq!(idx3, idx1); // Should reuse idx1
    }

    #[test]
    fn test_function_table() {
        let mut table = FunctionTable::new();

        let idx = table.allocate(0x1000, 0, 1);
        assert_eq!(table.get_code_ptr(idx), Some(0x1000));

        let entry = table.get_entry(idx).unwrap();
        assert_eq!(entry.module_id, 0);
        assert_eq!(entry.version, 1);
        assert!(entry.is_valid());

        table.mark_tombstone(idx);
        assert_eq!(table.get_code_ptr(idx), None);
    }

    #[test]
    fn test_global_table() {
        let mut table = GlobalTable::new();

        let idx = table.allocate(0x2000, 64, 1);
        assert_eq!(table.get_data_ptr(idx), Some(0x2000));

        let entry = table.get_entry(idx).unwrap();
        assert_eq!(entry.size, 64);
        assert_eq!(entry.module_id, 1);
    }

    #[test]
    fn test_type_table() {
        let mut table = TypeTable::new();

        let idx = table.allocate(0x3000, 0xDEADBEEF, 2);
        assert_eq!(table.get_type_ptr(idx), Some(0x3000));
        assert_eq!(table.get_layout_hash(idx), Some(0xDEADBEEF));
    }
}
