//! Bounded scalar views of the hosted RuntimeDict provider (kind 3).
//!
//! The admission table is an allocation-lifecycle index, not an insertion
//! mirror. Slot order and storage facts always come from the real dictionary.
//! Reads never allocate, wait for a lock, or call general RuntimeValue helpers.
//! A long collision chain refuses admission after 64 probes. Fuel measures
//! registry probes plus one scalar operation, not all machine instructions.

use super::collections::RuntimeString;
use super::core::RuntimeValue;
use super::dict::RuntimeDict;
use super::heap::{HeapInt, HeapObjectType};
use std::sync::{Mutex, OnceLock};

const PROBES: usize = 64;
const READ_BOUND: i64 = (3 * PROBES + 1) as i64;
const TOMBSTONE: usize = 1;

#[derive(Clone, Copy, Default)]
struct Entry {
    addr: usize,
    kind: u8,
    // Allocation bytes for String/Int; descriptor index for Dict.
    bytes: u32,
}

#[derive(Clone, Copy, Default)]
struct Descriptor {
    owner: i64,
    epoch: i64,
    backing: i64,
    storage: usize,
    capacity: u64,
    mutations: u32,
}

#[derive(Default)]
struct Registry {
    slots: Vec<Entry>,
    occupied: usize,
    tombstones: usize,
    next_id: i64,
    dictionaries: Vec<Descriptor>,
    free_descriptors: Vec<usize>,
}

impl Registry {
    fn token(&mut self) -> i64 {
        let token = self.next_id;
        if token <= 0 {
            return 0;
        }
        self.next_id = token.checked_add(1).unwrap_or(0);
        token
    }

    fn bucket(addr: usize, capacity: usize) -> usize {
        let x = (addr >> 3).wrapping_mul(0x9e37_79b9usize);
        (x ^ (x >> 16)) & (capacity - 1)
    }

    fn insert_existing(&mut self, entry: Entry) {
        let mut index = Self::bucket(entry.addr, self.slots.len());
        loop {
            if self.slots[index].addr <= TOMBSTONE {
                if self.slots[index].addr == TOMBSTONE {
                    self.tombstones -= 1;
                }
                self.slots[index] = entry;
                self.occupied += 1;
                return;
            }
            index = (index + 1) & (self.slots.len() - 1);
        }
    }

    fn register(&mut self, addr: usize, kind: u8, bytes: u32) {
        if self.slots.is_empty() || self.occupied + self.tombstones >= self.slots.len() - self.slots.len() / 4 {
            // Compact deletion-heavy tables at their current capacity. Live
            // occupancy alone must not hide a table full of tombstones.
            let capacity = if self.occupied >= self.slots.len() / 2 {
                let Some(capacity) = self.slots.len().checked_mul(2) else {
                    self.next_id = 0;
                    return;
                };
                capacity
            } else {
                self.slots.len()
            };
            let capacity = capacity.max(128);
            let old = std::mem::replace(&mut self.slots, vec![Entry::default(); capacity]);
            self.occupied = 0;
            self.tombstones = 0;
            for entry in old {
                if entry.addr > TOMBSTONE {
                    self.insert_existing(entry);
                }
            }
        }
        let bytes = if kind == HeapObjectType::Dict as u8 {
            if bytes as usize != std::mem::size_of::<RuntimeDict>() {
                return;
            }
            let index = self.free_descriptors.pop().unwrap_or(self.dictionaries.len());
            let Ok(encoded) = u32::try_from(index) else {
                return;
            };
            let owner = self.token();
            // The canonical allocation hook receives an initialized real Dict.
            let dict = unsafe { &*(addr as *const RuntimeDict) };
            let descriptor = Descriptor {
                owner,
                epoch: 1,
                backing: owner,
                storage: dict.data as usize,
                capacity: dict.capacity,
                mutations: 0,
            };
            if index == self.dictionaries.len() {
                self.dictionaries.push(descriptor);
            } else {
                self.dictionaries[index] = descriptor;
            }
            encoded
        } else {
            bytes
        };
        self.insert_existing(Entry { addr, kind, bytes });
    }

    fn find(&self, addr: usize, fuel: &mut i64) -> Option<usize> {
        if addr <= TOMBSTONE || self.slots.is_empty() {
            return None;
        }
        let mut index = Self::bucket(addr, self.slots.len());
        for _ in 0..PROBES {
            if *fuel <= 0 {
                return None;
            }
            *fuel -= 1;
            let entry = self.slots[index];
            if entry.addr == 0 {
                return None;
            }
            if entry.addr == addr {
                return Some(index);
            }
            index = (index + 1) & (self.slots.len() - 1);
        }
        None
    }

    // Lifecycle changes are outside a read invocation and must find even an
    // entry that the bounded reader refuses because of a long collision tail.
    fn lifecycle_index(&self, addr: usize) -> Option<usize> {
        self.lifecycle_lookup(addr).0
    }

    fn lifecycle_lookup(&self, addr: usize) -> (Option<usize>, usize) {
        if self.slots.is_empty() {
            return (None, 0);
        }
        let mut index = Self::bucket(addr, self.slots.len());
        for probe in 0..self.slots.len() {
            if self.slots[index].addr == 0 {
                return (None, probe + 1);
            }
            if self.slots[index].addr == addr {
                return (Some(index), probe + 1);
            }
            index = (index + 1) & (self.slots.len() - 1);
        }
        (None, self.slots.len())
    }

    fn unregister(&mut self, addr: usize) {
        if let Some(index) = self.lifecycle_index(addr) {
            let entry = self.slots[index];
            if entry.kind == HeapObjectType::Dict as u8 {
                self.dictionaries[entry.bytes as usize] = Descriptor::default();
                self.free_descriptors.push(entry.bytes as usize);
            }
            self.slots[index] = Entry {
                addr: TOMBSTONE,
                ..Entry::default()
            };
            self.occupied -= 1;
            self.tombstones += 1;
        }
    }
}

static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
fn registry() -> &'static Mutex<Registry> {
    REGISTRY.get_or_init(|| {
        Mutex::new(Registry {
            next_id: 1,
            ..Registry::default()
        })
    })
}

/// Called only after the canonical heap registry admits a real allocation.
pub(super) fn registered(addr: usize, kind: u8, bytes: u32) {
    if !indexed_kind(kind) {
        return;
    }
    if let Ok(mut registry) = registry().lock() {
        registry.register(addr, kind, bytes);
    }
}

/// Called before deallocation, including generic/transient frees.
pub(super) fn unregistered(addr: usize, kind: u8) {
    // Arrays, tuples, objects and other unrelated frees never probe this index.
    if !indexed_kind(kind) {
        return;
    }
    if let Some(registry) = REGISTRY.get() {
        if let Ok(mut registry) = registry.lock() {
            registry.unregister(addr);
        }
    }
}

fn indexed_kind(kind: u8) -> bool {
    kind == HeapObjectType::Dict as u8 || kind == HeapObjectType::String as u8 || kind == HeapObjectType::Int as u8
}

pub(super) fn cleared() {
    if let Some(registry) = REGISTRY.get() {
        if let Ok(mut registry) = registry.lock() {
            registry.slots.fill(Entry::default());
            registry.occupied = 0;
            registry.tombstones = 0;
            registry.dictionaries.clear();
            registry.free_descriptors.clear();
            // Never reset next_id: old owners cannot authenticate reused addresses.
        }
    }
}

/// Mutations remain usable after overflow; only scalar reader admission closes.
/// The scoped marker closes admission throughout writes and backing release.
pub(super) struct Mutation(usize);

pub(super) fn mutation(dict: *mut RuntimeDict) -> Mutation {
    if let Ok(mut registry) = registry().lock() {
        if let Some(index) = registry.lifecycle_index(dict as usize) {
            let descriptor = registry.slots[index].bytes as usize;
            let entry = &mut registry.dictionaries[descriptor];
            entry.epoch = if entry.epoch <= 0 {
                0
            } else {
                entry.epoch.checked_add(1).unwrap_or(0)
            };
            if let Some(mutations) = entry.mutations.checked_add(1) {
                entry.mutations = mutations;
            } else {
                entry.epoch = 0;
            }
        }
    }
    Mutation(dict as usize)
}

impl Drop for Mutation {
    fn drop(&mut self) {
        if let Ok(mut registry) = registry().lock() {
            if let Some(index) = registry.lifecycle_index(self.0) {
                let descriptor = registry.slots[index].bytes as usize;
                registry.dictionaries[descriptor].mutations =
                    registry.dictionaries[descriptor].mutations.saturating_sub(1);
            }
        }
    }
}

pub(super) fn storage_replaced(dict: *mut RuntimeDict) {
    if let Ok(mut registry) = registry().lock() {
        if let Some(index) = registry.lifecycle_index(dict as usize) {
            let descriptor = registry.slots[index].bytes as usize;
            let backing = registry.token();
            let entry = &mut registry.dictionaries[descriptor];
            entry.backing = backing;
            entry.storage = unsafe { (*dict).data as usize };
            entry.capacity = unsafe { (*dict).capacity };
            if backing == 0 {
                entry.epoch = 0;
            }
        }
    }
}

fn address(value: RuntimeValue) -> Option<usize> {
    if !value.is_heap() {
        return None;
    }
    let addr = value.as_heap_ptr() as usize;
    if addr < 4096 || addr & 7 != 0 {
        None
    } else {
        Some(addr)
    }
}

fn admitted(
    registry: &Registry,
    dict: RuntimeValue,
    owner: Option<i64>,
    epoch: Option<i64>,
    fuel: &mut i64,
) -> Option<(usize, Descriptor)> {
    let addr = address(dict)?;
    let entry = registry.slots[registry.find(addr, fuel)?];
    if entry.kind != HeapObjectType::Dict as u8 {
        return None;
    }
    let entry = *registry.dictionaries.get(entry.bytes as usize)?;
    if entry.owner <= 0
        || entry.epoch <= 0
        || entry.backing <= 0
        || entry.mutations != 0
        || owner.is_some_and(|x| x != entry.owner)
        || epoch.is_some_and(|x| x != entry.epoch)
    {
        return None;
    }
    // Membership and owner checks precede every target dereference. The guard
    // also prevents an unregister/deallocation from passing this read.
    let dict = unsafe { &*(addr as *const RuntimeDict) };
    let bytes = dict
        .capacity
        .checked_mul(2 * std::mem::size_of::<RuntimeValue>() as u64)?;
    if dict.capacity != entry.capacity
        || dict.data as usize != entry.storage
        || dict.len > dict.capacity
        || dict.capacity == 0
        || dict.data.is_null()
        || bytes > isize::MAX as u64
        || bytes > i64::MAX as u64
    {
        return None;
    }
    Some((addr, entry))
}

fn read(
    dict: RuntimeValue,
    owner: Option<i64>,
    epoch: Option<i64>,
    mut fuel: i64,
    operation: impl FnOnce(&Registry, usize, Descriptor, &mut i64) -> Option<i64>,
) -> i64 {
    // Exact bound is required even if this particular lookup would be shorter.
    // A caller cannot spend less than the reservation advertised by bound().
    if fuel < READ_BOUND {
        return -1;
    }
    fuel = READ_BOUND - 1;
    let Some(registry) = REGISTRY.get() else {
        return -1;
    };
    let Ok(registry) = registry.try_lock() else {
        return -1;
    };
    admitted(&registry, dict, owner, epoch, &mut fuel)
        .and_then(|(addr, entry)| operation(&registry, addr, entry, &mut fuel))
        .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_dict_scope_read_bound_v1() -> i64 {
    READ_BOUND
}

#[no_mangle]
pub extern "C" fn rt_dict_scope_read_owner_v1(dict: RuntimeValue, fuel: i64) -> i64 {
    read(dict, None, None, fuel, |_, _, entry, _| Some(entry.owner))
}

#[no_mangle]
pub extern "C" fn rt_dict_scope_read_epoch_v1(dict: RuntimeValue, owner: i64, fuel: i64) -> i64 {
    read(dict, Some(owner), None, fuel, |_, _, entry, _| Some(entry.epoch))
}

#[no_mangle]
pub extern "C" fn rt_dict_scope_read_meta_v1(dict: RuntimeValue, owner: i64, epoch: i64, field: i64, fuel: i64) -> i64 {
    read(dict, Some(owner), Some(epoch), fuel, |_, addr, entry, _| {
        let dict = unsafe { &*(addr as *const RuntimeDict) };
        match field {
            0 => Some(3),
            1 => i64::try_from(dict.len).ok(),
            2 | 3 => i64::try_from(dict.capacity).ok(),
            4 => Some(entry.backing),
            5 => Some(std::mem::size_of::<RuntimeDict>() as i64),
            6 => dict
                .capacity
                .checked_mul(2 * std::mem::size_of::<RuntimeValue>() as u64)
                .and_then(|x| i64::try_from(x).ok()),
            _ => None,
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_dict_scope_read_slot_v1(
    dict: RuntimeValue,
    owner: i64,
    epoch: i64,
    slot: i64,
    field: i64,
    byte_index: i64,
    fuel: i64,
) -> i64 {
    read(dict, Some(owner), Some(epoch), fuel, |registry, addr, _, fuel| {
        let dict = unsafe { &*(addr as *const RuntimeDict) };
        if slot < 0 || slot as u64 >= dict.capacity || !(0..=3).contains(&field) {
            return None;
        }
        let key = unsafe { *dict.data.add(slot as usize * 2) };
        if key.is_nil() {
            return if field == 0 { Some(0) } else { None };
        }
        let key_addr = address(key)?;
        let key_entry = registry.slots[registry.find(key_addr, fuel)?];
        if key_entry.kind != HeapObjectType::String as u8
            || (key_entry.bytes as usize) < std::mem::size_of::<RuntimeString>()
        {
            return None;
        }
        let text = unsafe { &*(key_addr as *const RuntimeString) };
        if text.len > key_entry.bytes as u64 - std::mem::size_of::<RuntimeString>() as u64 {
            return None;
        }
        let value = unsafe { *dict.data.add(slot as usize * 2 + 1) };
        let symbol = if value.is_int() {
            (value.to_raw() as i64) >> 3
        } else {
            let value_addr = address(value)?;
            let value_entry = registry.slots[registry.find(value_addr, fuel)?];
            if value_entry.kind != HeapObjectType::Int as u8
                || value_entry.bytes as usize != std::mem::size_of::<HeapInt>()
            {
                return None;
            }
            unsafe { (*(value_addr as *const HeapInt)).value }
        };
        if symbol < 0 {
            return None;
        }
        match field {
            0 => Some(1),
            1 => Some(symbol),
            2 => i64::try_from(text.len).ok(),
            3 if byte_index >= 0 && (byte_index as u64) < text.len => {
                Some(unsafe { *((text as *const RuntimeString).add(1) as *const u8).add(byte_index as usize) } as i64)
            }
            _ => None,
        }
    })
}

#[cfg(test)]
#[path = "dict_scope_read_tests.rs"]
mod tests;
