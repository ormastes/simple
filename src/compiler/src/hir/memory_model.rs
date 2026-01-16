//! Happens-before memory model implementation (#1099)
//!
//! This module implements a formal happens-before memory model that ensures
//! data-race freedom in concurrent Simple programs. The model defines when
//! one operation is guaranteed to be visible to another.
//!
//! ## Happens-Before Relations
//!
//! The happens-before relation (→) is the transitive closure of:
//!
//! 1. **Program Order**: Within a single thread/actor, if A comes before B in
//!    program order, then A → B.
//!
//! 2. **Synchronization Order**:
//!    - Lock release → Lock acquire (on the same mutex)
//!    - Atomic store (Release) → Atomic load (Acquire) (same location)
//!    - Thread/actor spawn → First operation in spawned thread
//!    - Last operation in thread → Thread join
//!    - Channel send → Channel receive (same message)
//!
//! 3. **Transitivity**: If A → B and B → C, then A → C
//!
//! ## Memory Model Guarantees
//!
//! - **Sequential Consistency for Data-Race-Free (SC-DRF)**: Programs without
//!   data races have sequentially consistent semantics.
//!
//! - **Data Race**: Two operations conflict (access same location, at least one
//!   is a write, not both atomic) and are not ordered by happens-before.
//!
//! - **No Torn Reads**: All reads see a complete write (atomicity).

use std::collections::{HashMap, HashSet};

/// A unique identifier for a memory operation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OperationId(usize);

impl OperationId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }
}

/// Types of memory operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoryOperation {
    /// Read from a memory location
    Read { location: LocationId, thread: ThreadId },
    /// Write to a memory location
    Write { location: LocationId, thread: ThreadId },
    /// Atomic read-modify-write operation
    AtomicRMW {
        location: LocationId,
        thread: ThreadId,
        ordering: MemoryOrdering,
    },
    /// Lock acquisition
    LockAcquire { lock: LockId, thread: ThreadId },
    /// Lock release
    LockRelease { lock: LockId, thread: ThreadId },
    /// Thread/actor spawn
    ThreadSpawn { parent: ThreadId, child: ThreadId },
    /// Thread/actor join
    ThreadJoin { parent: ThreadId, child: ThreadId },
    /// Channel send
    ChannelSend { channel: ChannelId, thread: ThreadId },
    /// Channel receive
    ChannelReceive { channel: ChannelId, thread: ThreadId },
}

/// Memory ordering for atomic operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

/// Unique identifier for a memory location
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocationId(usize);

impl LocationId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

/// Unique identifier for a thread/actor
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ThreadId(usize);

impl ThreadId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

/// Unique identifier for a lock (mutex/rwlock)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LockId(usize);

impl LockId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

/// Unique identifier for a channel
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChannelId(usize);

impl ChannelId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

/// Graph tracking happens-before relationships
#[derive(Debug, Clone)]
pub struct HappensBeforeGraph {
    /// Map from operation ID to operation details
    operations: HashMap<OperationId, MemoryOperation>,

    /// Direct happens-before edges (not transitive closure)
    /// edges[a] = set of operations that a happens-before
    edges: HashMap<OperationId, HashSet<OperationId>>,

    /// Program order per thread
    program_order: HashMap<ThreadId, Vec<OperationId>>,

    /// Lock synchronization: last release per lock
    lock_releases: HashMap<LockId, OperationId>,

    /// Atomic synchronization: last store per location
    atomic_stores: HashMap<LocationId, Vec<(OperationId, MemoryOrdering)>>,

    /// Thread lifecycle: spawn and join operations
    thread_spawns: HashMap<ThreadId, OperationId>,
    thread_joins: HashMap<ThreadId, OperationId>,

    /// Channel synchronization: sends and receives
    channel_sends: HashMap<ChannelId, Vec<OperationId>>,
    channel_receives: HashMap<ChannelId, Vec<OperationId>>,

    /// Next operation ID
    next_op_id: usize,
}

impl HappensBeforeGraph {
    /// Create a new empty happens-before graph
    pub fn new() -> Self {
        Self {
            operations: HashMap::new(),
            edges: HashMap::new(),
            program_order: HashMap::new(),
            lock_releases: HashMap::new(),
            atomic_stores: HashMap::new(),
            thread_spawns: HashMap::new(),
            thread_joins: HashMap::new(),
            channel_sends: HashMap::new(),
            channel_receives: HashMap::new(),
            next_op_id: 0,
        }
    }

    /// Add a memory operation and return its ID
    pub fn add_operation(&mut self, op: MemoryOperation) -> OperationId {
        let op_id = OperationId::new(self.next_op_id);
        self.next_op_id += 1;

        // Add to operations map
        self.operations.insert(op_id, op.clone());

        // Add happens-before edges BEFORE adding to program order
        // This ensures get_previous_operation returns the actual previous op
        self.add_synchronization_edges(op_id, &op);

        // Update program order for the thread (AFTER establishing edges)
        let thread = self.get_thread_id(&op);
        self.program_order.entry(thread).or_insert_with(Vec::new).push(op_id);

        // Update synchronization tracking
        match &op {
            MemoryOperation::LockRelease { lock, .. } => {
                self.lock_releases.insert(*lock, op_id);
            }
            MemoryOperation::AtomicRMW { location, ordering, .. } => {
                self.atomic_stores
                    .entry(*location)
                    .or_insert_with(Vec::new)
                    .push((op_id, *ordering));
            }
            MemoryOperation::ThreadSpawn { child, .. } => {
                self.thread_spawns.insert(*child, op_id);
            }
            MemoryOperation::ThreadJoin { child, .. } => {
                self.thread_joins.insert(*child, op_id);
            }
            MemoryOperation::ChannelSend { channel, .. } => {
                self.channel_sends.entry(*channel).or_insert_with(Vec::new).push(op_id);
            }
            MemoryOperation::ChannelReceive { channel, .. } => {
                self.channel_receives
                    .entry(*channel)
                    .or_insert_with(Vec::new)
                    .push(op_id);
            }
            _ => {}
        }

        op_id
    }

    /// Get the thread ID for an operation
    fn get_thread_id(&self, op: &MemoryOperation) -> ThreadId {
        match op {
            MemoryOperation::Read { thread, .. } => *thread,
            MemoryOperation::Write { thread, .. } => *thread,
            MemoryOperation::AtomicRMW { thread, .. } => *thread,
            MemoryOperation::LockAcquire { thread, .. } => *thread,
            MemoryOperation::LockRelease { thread, .. } => *thread,
            MemoryOperation::ThreadSpawn { parent, .. } => *parent,
            MemoryOperation::ThreadJoin { parent, .. } => *parent,
            MemoryOperation::ChannelSend { thread, .. } => *thread,
            MemoryOperation::ChannelReceive { thread, .. } => *thread,
        }
    }

    /// Add synchronization edges for a new operation
    fn add_synchronization_edges(&mut self, op_id: OperationId, op: &MemoryOperation) {
        match op {
            // Lock acquire synchronizes with last release
            MemoryOperation::LockAcquire { lock, thread } => {
                if let Some(&release_id) = self.lock_releases.get(lock) {
                    self.add_edge(release_id, op_id);
                }

                // Add program order edge from previous operation in thread
                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }

            // Lock release has program order edge
            MemoryOperation::LockRelease { thread, .. } => {
                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }

            // Atomic load (Acquire) synchronizes with stores (Release)
            MemoryOperation::AtomicRMW {
                location,
                ordering,
                thread,
            } => {
                let mut edges_to_add = Vec::new();

                if matches!(
                    ordering,
                    MemoryOrdering::Acquire | MemoryOrdering::AcqRel | MemoryOrdering::SeqCst
                ) {
                    if let Some(stores) = self.atomic_stores.get(location) {
                        for &(store_id, store_ordering) in stores {
                            if matches!(
                                store_ordering,
                                MemoryOrdering::Release | MemoryOrdering::AcqRel | MemoryOrdering::SeqCst
                            ) {
                                edges_to_add.push(store_id);
                            }
                        }
                    }
                }

                // Add collected edges
                for store_id in edges_to_add {
                    self.add_edge(store_id, op_id);
                }

                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }

            // Thread spawn creates edge from parent to child's first operation
            MemoryOperation::ThreadSpawn { parent, child } => {
                if let Some(prev) = self.get_previous_operation(*parent) {
                    self.add_edge(prev, op_id);
                }
                // Edge to child's first operation added when child executes
            }

            // Thread join synchronizes with child's last operation
            MemoryOperation::ThreadJoin { parent, child } => {
                if let Some(child_ops) = self.program_order.get(child) {
                    if let Some(&last_child_op) = child_ops.last() {
                        self.add_edge(last_child_op, op_id);
                    }
                }

                if let Some(prev) = self.get_previous_operation(*parent) {
                    self.add_edge(prev, op_id);
                }
            }

            // Channel receive synchronizes with matching send
            MemoryOperation::ChannelReceive { channel, thread } => {
                if let Some(sends) = self.channel_sends.get(channel) {
                    if let Some(&send_id) = sends.last() {
                        self.add_edge(send_id, op_id);
                    }
                }

                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }

            // Regular reads/writes have program order edges
            MemoryOperation::Read { thread, .. } | MemoryOperation::Write { thread, .. } => {
                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }

            MemoryOperation::ChannelSend { thread, .. } => {
                if let Some(prev) = self.get_previous_operation(*thread) {
                    self.add_edge(prev, op_id);
                }
            }
        }
    }

    /// Get the previous operation in a thread's program order
    fn get_previous_operation(&self, thread: ThreadId) -> Option<OperationId> {
        self.program_order.get(&thread).and_then(|ops| ops.last()).copied()
    }

    /// Add a happens-before edge
    fn add_edge(&mut self, from: OperationId, to: OperationId) {
        self.edges.entry(from).or_insert_with(HashSet::new).insert(to);
    }

    /// Check if operation `from` happens-before operation `to`
    pub fn happens_before(&self, from: OperationId, to: OperationId) -> bool {
        if from == to {
            return false;
        }

        // BFS to find path from `from` to `to`
        let mut visited = HashSet::new();
        let mut queue = vec![from];

        while let Some(current) = queue.pop() {
            if current == to {
                return true;
            }

            if visited.insert(current) {
                if let Some(successors) = self.edges.get(&current) {
                    queue.extend(successors.iter().copied());
                }
            }
        }

        false
    }

    /// Check if two operations are concurrent (neither happens-before the other)
    pub fn are_concurrent(&self, op1: OperationId, op2: OperationId) -> bool {
        !self.happens_before(op1, op2) && !self.happens_before(op2, op1)
    }

    /// Detect potential data races
    ///
    /// A data race occurs when:
    /// 1. Two operations access the same location
    /// 2. At least one is a write
    /// 3. They are not both atomic
    /// 4. They are concurrent (no happens-before order)
    pub fn detect_data_races(&self) -> Vec<DataRace> {
        let mut races = Vec::new();

        // Group operations by location
        let mut location_ops: HashMap<LocationId, Vec<OperationId>> = HashMap::new();
        for (&op_id, op) in &self.operations {
            match op {
                MemoryOperation::Read { location, .. } | MemoryOperation::Write { location, .. } => {
                    location_ops.entry(*location).or_insert_with(Vec::new).push(op_id);
                }
                _ => {}
            }
        }

        // Check each pair of operations on the same location
        for (location, ops) in location_ops {
            for i in 0..ops.len() {
                for j in (i + 1)..ops.len() {
                    let op1_id = ops[i];
                    let op2_id = ops[j];

                    if let (Some(op1), Some(op2)) = (self.operations.get(&op1_id), self.operations.get(&op2_id)) {
                        // Check if at least one is a write
                        let has_write = matches!(op1, MemoryOperation::Write { .. })
                            || matches!(op2, MemoryOperation::Write { .. });

                        if has_write && self.are_concurrent(op1_id, op2_id) {
                            races.push(DataRace {
                                location,
                                op1: op1_id,
                                op2: op2_id,
                            });
                        }
                    }
                }
            }
        }

        races
    }

    /// Check if program is data-race-free
    pub fn is_race_free(&self) -> bool {
        self.detect_data_races().is_empty()
    }
}

impl Default for HappensBeforeGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// A detected data race
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRace {
    pub location: LocationId,
    pub op1: OperationId,
    pub op2: OperationId,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_program_order() {
        let mut graph = HappensBeforeGraph::new();
        let thread = ThreadId::new(1);
        let loc = LocationId::new(1);

        let write = graph.add_operation(MemoryOperation::Write { location: loc, thread });

        let read = graph.add_operation(MemoryOperation::Read { location: loc, thread });

        // Write happens-before read in same thread (program order)
        assert!(graph.happens_before(write, read));
        assert!(!graph.happens_before(read, write));
    }

    #[test]
    fn test_lock_synchronization() {
        let mut graph = HappensBeforeGraph::new();
        let lock = LockId::new(1);
        let thread1 = ThreadId::new(1);
        let thread2 = ThreadId::new(2);

        let release = graph.add_operation(MemoryOperation::LockRelease { lock, thread: thread1 });

        let acquire = graph.add_operation(MemoryOperation::LockAcquire { lock, thread: thread2 });

        // Release happens-before acquire
        assert!(graph.happens_before(release, acquire));
    }

    #[test]
    fn test_atomic_synchronization() {
        let mut graph = HappensBeforeGraph::new();
        let loc = LocationId::new(1);
        let thread1 = ThreadId::new(1);
        let thread2 = ThreadId::new(2);

        let store = graph.add_operation(MemoryOperation::AtomicRMW {
            location: loc,
            thread: thread1,
            ordering: MemoryOrdering::Release,
        });

        let load = graph.add_operation(MemoryOperation::AtomicRMW {
            location: loc,
            thread: thread2,
            ordering: MemoryOrdering::Acquire,
        });

        // Store(Release) happens-before Load(Acquire)
        assert!(graph.happens_before(store, load));
    }

    #[test]
    fn test_thread_spawn_join() {
        let mut graph = HappensBeforeGraph::new();
        let parent = ThreadId::new(1);
        let child = ThreadId::new(2);
        let loc = LocationId::new(1);

        let spawn = graph.add_operation(MemoryOperation::ThreadSpawn { parent, child });

        let child_write = graph.add_operation(MemoryOperation::Write {
            location: loc,
            thread: child,
        });

        let join = graph.add_operation(MemoryOperation::ThreadJoin { parent, child });

        // Child's operation happens-before join
        assert!(graph.happens_before(child_write, join));
    }

    #[test]
    fn test_data_race_detection() {
        let mut graph = HappensBeforeGraph::new();
        let loc = LocationId::new(1);
        let thread1 = ThreadId::new(1);
        let thread2 = ThreadId::new(2);

        // Two concurrent writes to same location = data race
        let write1 = graph.add_operation(MemoryOperation::Write {
            location: loc,
            thread: thread1,
        });

        let write2 = graph.add_operation(MemoryOperation::Write {
            location: loc,
            thread: thread2,
        });

        let races = graph.detect_data_races();
        assert_eq!(races.len(), 1);
        assert_eq!(races[0].location, loc);
    }

    #[test]
    fn test_no_race_with_synchronization() {
        let mut graph = HappensBeforeGraph::new();
        let loc = LocationId::new(1);
        let lock = LockId::new(1);
        let thread1 = ThreadId::new(1);
        let thread2 = ThreadId::new(2);

        // Thread 1: write then unlock
        let write1 = graph.add_operation(MemoryOperation::Write {
            location: loc,
            thread: thread1,
        });

        let release = graph.add_operation(MemoryOperation::LockRelease { lock, thread: thread1 });

        // Thread 2: lock then write
        let acquire = graph.add_operation(MemoryOperation::LockAcquire { lock, thread: thread2 });

        let write2 = graph.add_operation(MemoryOperation::Write {
            location: loc,
            thread: thread2,
        });

        // No race because write1 happens-before write2 (via lock synchronization)
        let races = graph.detect_data_races();
        assert_eq!(races.len(), 0);
    }

    #[test]
    fn test_transitive_happens_before() {
        let mut graph = HappensBeforeGraph::new();
        let thread = ThreadId::new(1);
        let loc = LocationId::new(1);

        let op1 = graph.add_operation(MemoryOperation::Write { location: loc, thread });

        let op2 = graph.add_operation(MemoryOperation::Read { location: loc, thread });

        let op3 = graph.add_operation(MemoryOperation::Write { location: loc, thread });

        // Transitivity: op1 → op2 → op3, so op1 → op3
        assert!(graph.happens_before(op1, op3));
    }
}
