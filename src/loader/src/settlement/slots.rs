//! Slot-based memory allocator for settlement regions.
//!
//! Manages memory in fixed-size slots for efficient allocation and compaction.

/// Default slot sizes for different regions.
pub const CODE_SLOT_SIZE: usize = 64 * 1024; // 64KB for code
pub const DATA_SLOT_SIZE: usize = 16 * 1024; // 16KB for data
pub const TABLE_SLOT_SIZE: usize = 4 * 1024; // 4KB for tables

/// A range of consecutive slots.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlotRange {
    /// Starting slot index
    pub start: usize,
    /// Number of slots
    pub count: usize,
}

impl SlotRange {
    pub fn new(start: usize, count: usize) -> Self {
        Self { start, count }
    }

    pub fn end(&self) -> usize {
        self.start + self.count
    }

    pub fn contains(&self, slot: usize) -> bool {
        slot >= self.start && slot < self.end()
    }

    pub fn overlaps(&self, other: &SlotRange) -> bool {
        self.start < other.end() && other.start < self.end()
    }
}

/// Slot-based memory allocator.
///
/// Manages a region of memory divided into fixed-size slots.
/// Uses a bitmap for tracking occupied slots.
pub struct SlotAllocator {
    /// Base address of managed region
    base: *mut u8,
    /// Size of each slot in bytes
    slot_size: usize,
    /// Total number of slots
    total_slots: usize,
    /// Bitmap: 1 bit per slot, 1 = occupied, 0 = free
    bitmap: Vec<u64>,
    /// Number of free slots (cached for performance)
    free_count: usize,
    /// Total region size
    region_size: usize,
}

impl SlotAllocator {
    /// Create a new slot allocator.
    ///
    /// # Arguments
    /// * `base` - Base address of the memory region
    /// * `region_size` - Total size of the region in bytes
    /// * `slot_size` - Size of each slot in bytes
    pub fn new(base: *mut u8, region_size: usize, slot_size: usize) -> Self {
        let total_slots = region_size / slot_size;
        let bitmap_words = (total_slots + 63) / 64;

        Self {
            base,
            slot_size,
            total_slots,
            bitmap: vec![0; bitmap_words],
            free_count: total_slots,
            region_size,
        }
    }

    /// Get the base address.
    pub fn base(&self) -> *mut u8 {
        self.base
    }

    /// Get slot size.
    pub fn slot_size(&self) -> usize {
        self.slot_size
    }

    /// Get total number of slots.
    pub fn total_slots(&self) -> usize {
        self.total_slots
    }

    /// Get number of free slots.
    pub fn free_slots(&self) -> usize {
        self.free_count
    }

    /// Get number of used slots.
    pub fn used_slots(&self) -> usize {
        self.total_slots - self.free_count
    }

    /// Calculate how many slots are needed for a given size.
    pub fn slots_needed(&self, size: usize) -> usize {
        (size + self.slot_size - 1) / self.slot_size
    }

    /// Convert a slot index to a memory address.
    pub fn slot_to_addr(&self, slot: usize) -> *mut u8 {
        unsafe { self.base.add(slot * self.slot_size) }
    }

    /// Convert a memory address to a slot index.
    pub fn addr_to_slot(&self, addr: *const u8) -> Option<usize> {
        let offset = addr as usize - self.base as usize;
        if offset < self.region_size {
            Some(offset / self.slot_size)
        } else {
            None
        }
    }

    /// Check if a slot is occupied.
    pub fn is_occupied(&self, slot: usize) -> bool {
        if slot >= self.total_slots {
            return true; // Out of bounds treated as occupied
        }
        let word = slot / 64;
        let bit = slot % 64;
        (self.bitmap[word] & (1 << bit)) != 0
    }

    /// Mark a slot as occupied.
    fn set_occupied(&mut self, slot: usize) {
        if slot < self.total_slots {
            let word = slot / 64;
            let bit = slot % 64;
            if (self.bitmap[word] & (1 << bit)) == 0 {
                self.bitmap[word] |= 1 << bit;
                self.free_count -= 1;
            }
        }
    }

    /// Mark a slot as free.
    fn set_free(&mut self, slot: usize) {
        if slot < self.total_slots {
            let word = slot / 64;
            let bit = slot % 64;
            if (self.bitmap[word] & (1 << bit)) != 0 {
                self.bitmap[word] &= !(1 << bit);
                self.free_count += 1;
            }
        }
    }

    /// Allocate a contiguous range of slots.
    ///
    /// Returns `None` if not enough contiguous slots are available.
    pub fn allocate(&mut self, slots_needed: usize) -> Option<SlotRange> {
        if slots_needed == 0 || slots_needed > self.free_count {
            return None;
        }

        // Simple first-fit algorithm
        let mut run_start = 0;
        let mut run_length = 0;

        for slot in 0..self.total_slots {
            if self.is_occupied(slot) {
                run_start = slot + 1;
                run_length = 0;
            } else {
                run_length += 1;
                if run_length >= slots_needed {
                    // Found a suitable range
                    let range = SlotRange::new(run_start, slots_needed);
                    for s in run_start..run_start + slots_needed {
                        self.set_occupied(s);
                    }
                    return Some(range);
                }
            }
        }

        None
    }

    /// Allocate slots for a given byte size.
    pub fn allocate_bytes(&mut self, size: usize) -> Option<SlotRange> {
        let slots = self.slots_needed(size);
        self.allocate(slots)
    }

    /// Free a range of slots.
    pub fn free(&mut self, range: SlotRange) {
        for slot in range.start..range.end() {
            self.set_free(slot);
        }
    }

    /// Get the memory range for a slot range.
    pub fn get_memory(&self, range: SlotRange) -> (*mut u8, usize) {
        let addr = self.slot_to_addr(range.start);
        let size = range.count * self.slot_size;
        (addr, size)
    }

    /// Find all free ranges (for defragmentation analysis).
    pub fn free_ranges(&self) -> Vec<SlotRange> {
        let mut ranges = Vec::new();
        let mut run_start = None;

        for slot in 0..self.total_slots {
            if self.is_occupied(slot) {
                if let Some(start) = run_start {
                    ranges.push(SlotRange::new(start, slot - start));
                    run_start = None;
                }
            } else if run_start.is_none() {
                run_start = Some(slot);
            }
        }

        // Handle trailing free range
        if let Some(start) = run_start {
            ranges.push(SlotRange::new(start, self.total_slots - start));
        }

        ranges
    }

    /// Find all occupied ranges.
    pub fn occupied_ranges(&self) -> Vec<SlotRange> {
        let mut ranges = Vec::new();
        let mut run_start = None;

        for slot in 0..self.total_slots {
            if !self.is_occupied(slot) {
                if let Some(start) = run_start {
                    ranges.push(SlotRange::new(start, slot - start));
                    run_start = None;
                }
            } else if run_start.is_none() {
                run_start = Some(slot);
            }
        }

        // Handle trailing occupied range
        if let Some(start) = run_start {
            ranges.push(SlotRange::new(start, self.total_slots - start));
        }

        ranges
    }

    /// Calculate fragmentation ratio (0.0 = no fragmentation, 1.0 = maximum).
    pub fn fragmentation(&self) -> f64 {
        let free_ranges = self.free_ranges();
        if self.free_count == 0 || free_ranges.is_empty() {
            return 0.0;
        }

        // Fragmentation = 1 - (largest_free_block / total_free)
        let largest_free = free_ranges.iter().map(|r| r.count).max().unwrap_or(0);
        1.0 - (largest_free as f64 / self.free_count as f64)
    }

    /// Defragment the allocator by computing move operations.
    ///
    /// Returns a list of (old_range, new_range) pairs describing moves needed.
    /// The caller is responsible for actually moving the data.
    pub fn defragment_plan(&self) -> Vec<(SlotRange, SlotRange)> {
        let mut moves = Vec::new();
        let occupied = self.occupied_ranges();

        let mut target_slot = 0;
        for range in occupied {
            if range.start != target_slot {
                // This range needs to move
                moves.push((range, SlotRange::new(target_slot, range.count)));
            }
            target_slot += range.count;
        }

        moves
    }

    /// Execute a defragmentation plan.
    ///
    /// This updates the bitmap but does NOT move the actual data.
    /// The caller must move the data before calling this.
    pub fn apply_defragment(&mut self, moves: &[(SlotRange, SlotRange)]) {
        for (old_range, new_range) in moves {
            // Free old slots
            for slot in old_range.start..old_range.end() {
                self.set_free(slot);
            }
            // Occupy new slots
            for slot in new_range.start..new_range.end() {
                self.set_occupied(slot);
            }
        }
    }
}

// Safety: SlotAllocator can be sent between threads if the base pointer is valid
unsafe impl Send for SlotAllocator {}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_allocator(total_slots: usize) -> SlotAllocator {
        // Use a dummy base address for testing
        SlotAllocator::new(
            0x10000 as *mut u8,
            total_slots * CODE_SLOT_SIZE,
            CODE_SLOT_SIZE,
        )
    }

    #[test]
    fn test_slot_range() {
        let range = SlotRange::new(5, 3);
        assert_eq!(range.start, 5);
        assert_eq!(range.count, 3);
        assert_eq!(range.end(), 8);
        assert!(range.contains(5));
        assert!(range.contains(7));
        assert!(!range.contains(8));
    }

    #[test]
    fn test_basic_allocation() {
        let mut alloc = make_allocator(10);
        assert_eq!(alloc.free_slots(), 10);

        let range = alloc.allocate(3).unwrap();
        assert_eq!(range.start, 0);
        assert_eq!(range.count, 3);
        assert_eq!(alloc.free_slots(), 7);

        let range2 = alloc.allocate(2).unwrap();
        assert_eq!(range2.start, 3);
        assert_eq!(alloc.free_slots(), 5);
    }

    #[test]
    fn test_allocation_failure() {
        let mut alloc = make_allocator(5);
        assert!(alloc.allocate(6).is_none());
        assert!(alloc.allocate(0).is_none());
    }

    #[test]
    fn test_free() {
        let mut alloc = make_allocator(10);
        let range = alloc.allocate(5).unwrap();
        assert_eq!(alloc.free_slots(), 5);

        alloc.free(range);
        assert_eq!(alloc.free_slots(), 10);
    }

    #[test]
    fn test_fragmentation() {
        let mut alloc = make_allocator(10);

        // Allocate 3 ranges
        let r1 = alloc.allocate(2).unwrap();
        let _r2 = alloc.allocate(2).unwrap();
        let r3 = alloc.allocate(2).unwrap();

        // Free alternating ranges to create fragmentation
        alloc.free(r1);
        alloc.free(r3);

        // Now we have: [free, free, used, used, free, free, free, free, free, free]
        let frag = alloc.fragmentation();
        assert!(frag > 0.0); // Should have some fragmentation
    }

    #[test]
    fn test_defragment_plan() {
        let mut alloc = make_allocator(10);

        // Create fragmented state
        let _r1 = alloc.allocate(2).unwrap();
        let r2 = alloc.allocate(2).unwrap();
        let _r3 = alloc.allocate(2).unwrap();

        // Free middle range
        alloc.free(r2);

        let plan = alloc.defragment_plan();
        // The last range (slots 4-5) should move to slots 2-3
        assert!(!plan.is_empty());
    }
}
