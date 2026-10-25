use super::*;
use super::super::collections::{rt_array_get, rt_array_len, rt_string_new};
use super::super::dict::{rt_dict_clear, rt_dict_free, rt_dict_keys, rt_dict_new, rt_dict_remove, rt_dict_set};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct CountedAllocator;
thread_local! {
    static COUNT: Cell<Option<usize>> = const { Cell::new(None) };
}
fn note_alloc() {
    let _ = COUNT.try_with(|count| {
        if let Some(n) = count.get() {
            count.set(Some(n + 1));
        }
    });
}
unsafe impl GlobalAlloc for CountedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        note_alloc();
        System.alloc(layout)
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        note_alloc();
        System.alloc_zeroed(layout)
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        note_alloc();
        System.realloc(ptr, layout, size)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
    }
}
#[global_allocator]
static ALLOCATOR: CountedAllocator = CountedAllocator;

fn text(value: &str) -> RuntimeValue {
    rt_string_new(value.as_ptr(), value.len() as u64)
}
fn view(dict: RuntimeValue) -> (i64, i64) {
    let owner = rt_dict_scope_read_owner_v1(dict, READ_BOUND);
    assert!(owner > 0);
    let epoch = rt_dict_scope_read_epoch_v1(dict, owner, READ_BOUND);
    assert!(epoch > 0);
    (owner, epoch)
}
fn slot(dict: RuntimeValue, owner: i64, epoch: i64, index: i64, field: i64, byte: i64) -> i64 {
    rt_dict_scope_read_slot_v1(dict, owner, epoch, index, field, byte, READ_BOUND)
}
fn first_live(dict: RuntimeValue, owner: i64, epoch: i64) -> i64 {
    let capacity = rt_dict_scope_read_meta_v1(dict, owner, epoch, 3, READ_BOUND);
    (0..capacity)
        .find(|index| slot(dict, owner, epoch, *index, 0, 0) == 1)
        .unwrap()
}
fn assert_canonical_projection(dict: RuntimeValue) {
    let (owner, epoch) = view(dict);
    let keys = rt_dict_keys(dict);
    let capacity = rt_dict_scope_read_meta_v1(dict, owner, epoch, 3, READ_BOUND);
    let mut ordinal = 0;
    for index in 0..capacity {
        let occupancy = slot(dict, owner, epoch, index, 0, 0);
        assert!((0..=1).contains(&occupancy));
        if occupancy == 0 {
            continue;
        }
        let canonical = rt_array_get(keys, ordinal);
        let canonical = unsafe { &*(canonical.as_heap_ptr() as *const RuntimeString) };
        let length = slot(dict, owner, epoch, index, 2, 0);
        assert_eq!(length, canonical.len as i64);
        for (byte, expected) in unsafe { canonical.as_bytes() }.iter().enumerate() {
            assert_eq!(slot(dict, owner, epoch, index, 3, byte as i64), *expected as i64);
        }
        ordinal += 1;
    }
    assert_eq!(ordinal, rt_array_len(keys));
}

#[test]
fn canonical_order_growth_remove_churn_clear_and_utf8_wide_ids() {
    let dict = rt_dict_new(0);
    assert_canonical_projection(dict);
    let (owner, epoch) = view(dict);
    assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch, 0, READ_BOUND), 3);
    assert_eq!(
        rt_dict_scope_read_meta_v1(dict, owner, epoch, 5, READ_BOUND),
        std::mem::size_of::<RuntimeDict>() as i64
    );
    assert_eq!(
        rt_dict_scope_read_meta_v1(dict, owner, epoch, 6, READ_BOUND),
        8 * 2 * std::mem::size_of::<RuntimeValue>() as i64
    );
    let backing = rt_dict_scope_read_meta_v1(dict, owner, epoch, 4, READ_BOUND);
    for id in 0..256 {
        assert!(rt_dict_set(
            dict,
            text(&format!("binding-{id}")),
            RuntimeValue::from_int(id)
        ));
    }
    let name = text("café猫");
    assert!(rt_dict_set(dict, name, RuntimeValue::from_int(i64::MAX)));
    let (same_owner, epoch) = view(dict);
    assert_eq!(owner, same_owner);
    assert_ne!(backing, rt_dict_scope_read_meta_v1(dict, owner, epoch, 4, READ_BOUND));
    assert_canonical_projection(dict);
    for id in (0..256).step_by(3) {
        assert!(!rt_dict_remove(dict, text(&format!("binding-{id}"))).is_nil());
    }
    assert_canonical_projection(dict);
    for id in 256..300 {
        assert!(rt_dict_set(
            dict,
            text(&format!("binding-{id}")),
            RuntimeValue::from_int(id)
        ));
    }
    assert_canonical_projection(dict);
    let (owner, epoch) = view(dict);
    let capacity = rt_dict_scope_read_meta_v1(dict, owner, epoch, 3, READ_BOUND);
    assert!((0..capacity).any(|i| slot(dict, owner, epoch, i, 1, 0) == i64::MAX));
    assert!(rt_dict_clear(dict));
    assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch, 1, READ_BOUND), -1);
    assert_canonical_projection(dict);
    assert!(rt_dict_set(dict, text("reinsert"), RuntimeValue::from_int(42)));
    assert_canonical_projection(dict);
    rt_dict_free(dict);
}

#[test]
fn refusal_fuel_type_staleness_forgery_and_freed_handles() {
    let dict = rt_dict_new(0);
    let key = text("scoped");
    assert!(rt_dict_set(dict, key, RuntimeValue::from_int(7)));
    let (owner, epoch) = view(dict);
    let index = first_live(dict, owner, epoch);
    assert_eq!(slot(dict, owner, epoch, index, 1, 0), 7);
    for fuel in [0, READ_BOUND - 1] {
        assert_eq!(rt_dict_scope_read_owner_v1(dict, fuel), -1);
        assert_eq!(rt_dict_scope_read_epoch_v1(dict, owner, fuel), -1);
        assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch, 0, fuel), -1);
        assert_eq!(rt_dict_scope_read_slot_v1(dict, owner, epoch, index, 1, 0, fuel), -1);
    }
    assert_eq!(rt_dict_scope_read_epoch_v1(dict, owner + 1, READ_BOUND), -1);
    assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch + 1, 0, READ_BOUND), -1);
    assert_eq!(slot(dict, owner, epoch, -1, 0, 0), -1);
    assert_eq!(slot(dict, owner, epoch, i64::MAX, 0, 0), -1);
    assert_eq!(slot(dict, owner, epoch, index, 3, -1), -1);
    assert_eq!(slot(dict, owner, epoch, index, 3, 6), -1);
    assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch, 7, READ_BOUND), -1);
    for bad in [
        RuntimeValue::NIL,
        RuntimeValue::from_int(9),
        RuntimeValue::from_raw(0x1005),
    ] {
        assert_eq!(rt_dict_scope_read_owner_v1(bad, READ_BOUND), -1);
    }
    for bad in [RuntimeValue::from_int(-1), text("wrong-value"), RuntimeValue::NIL] {
        assert!(rt_dict_set(dict, key, bad));
        assert_eq!(slot(dict, owner, epoch, index, 1, 0), -1);
        let (owner, epoch) = view(dict);
        let capacity = rt_dict_scope_read_meta_v1(dict, owner, epoch, 3, READ_BOUND);
        assert!((0..capacity).any(|i| slot(dict, owner, epoch, i, 0, 0) == -1));
    }
    assert!(rt_dict_clear(dict));
    assert!(rt_dict_set(dict, RuntimeValue::from_int(4), RuntimeValue::from_int(4)));
    let (owner, epoch) = view(dict);
    assert!((0..8).any(|i| slot(dict, owner, epoch, i, 0, 0) == -1));
    rt_dict_free(dict);
    assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
    assert_eq!(rt_dict_scope_read_epoch_v1(dict, owner, READ_BOUND), -1);
    // The same actual allocation address is unregistered/re-registered by
    // canonical lifecycle hooks; this deterministic ABA control does not
    // depend on an allocator choosing to recycle a freed block immediately.
    let replacement = rt_dict_new(0);
    let (old_owner, old_epoch) = view(replacement);
    let addr = replacement.as_heap_ptr() as usize;
    unregistered(addr, HeapObjectType::Dict as u8);
    registered(
        addr,
        HeapObjectType::Dict as u8,
        std::mem::size_of::<RuntimeDict>() as u32,
    );
    assert_ne!(view(replacement).0, old_owner);
    assert_eq!(
        rt_dict_scope_read_meta_v1(replacement, old_owner, old_epoch, 0, READ_BOUND),
        -1
    );
    rt_dict_free(replacement);
}

#[test]
fn collision_fuel_generation_overflow_and_epoch_overflow_latch() {
    let mut registry = Registry {
        slots: vec![Entry::default(); 128],
        next_id: 1,
        ..Registry::default()
    };
    let first = 4096;
    let bucket = Registry::bucket(first, 128);
    let collisions: Vec<_> = (4096..)
        .step_by(8)
        .filter(|addr| Registry::bucket(*addr, 128) == bucket)
        .take(PROBES + 1)
        .collect();
    for addr in &collisions {
        registry.insert_existing(Entry {
            addr: *addr,
            ..Entry::default()
        });
    }
    let mut fuel = READ_BOUND;
    assert!(registry.find(*collisions.last().unwrap(), &mut fuel).is_none());
    assert_eq!(fuel, READ_BOUND - PROBES as i64);
    registry.next_id = i64::MAX;
    assert_eq!(registry.token(), i64::MAX);
    assert_eq!(registry.token(), 0);
    assert_eq!(registry.token(), 0);
    let dict = rt_dict_new(0);
    let (owner, _) = view(dict);
    {
        let mut registry = super::registry().lock().unwrap();
        let index = registry.lifecycle_index(dict.as_heap_ptr() as usize).unwrap();
        let descriptor = registry.slots[index].bytes as usize;
        registry.dictionaries[descriptor].epoch = i64::MAX;
    }
    assert!(rt_dict_set(dict, text("overflow"), RuntimeValue::from_int(1)));
    assert_eq!(rt_dict_scope_read_epoch_v1(dict, owner, READ_BOUND), -1);
    assert!(rt_dict_clear(dict));
    assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
    rt_dict_free(dict);
}

#[test]
fn deletion_churn_compacts_used_slots_and_unrelated_frees_skip_registry() {
    let mut registry = Registry {
        next_id: 1,
        ..Registry::default()
    };
    let kind = HeapObjectType::String as u8;
    for index in 0..4096 {
        registry.register(4096 + index * 8, kind, 32);
    }
    let peak_capacity = registry.slots.len();
    for index in 0..4096 {
        registry.unregister(4096 + index * 8);
    }
    let mut max_absent_probes = 0;
    for index in 0..20_000 {
        let addr = 1_000_000 + index * 8;
        registry.register(addr, kind, 32);
        assert!(registry.occupied + registry.tombstones <= registry.slots.len() * 3 / 4);
        registry.unregister(addr);
        let (found, probes) = registry.lifecycle_lookup(9_000_000 + index * 8);
        assert!(found.is_none());
        max_absent_probes = max_absent_probes.max(probes);
    }
    assert_eq!(registry.occupied, 0);
    assert_eq!(registry.slots.len(), peak_capacity);
    assert!(
        max_absent_probes < 64,
        "absent lifecycle probes after sparse-live churn: {max_absent_probes}"
    );
    // An unrelated free must return before acquiring the private registry.
    let _locked = super::registry().lock().unwrap();
    unregistered(0x1000, HeapObjectType::Array as u8);
    println!("HOSTED_RUST_REGISTRY_CHURN peak_slots={peak_capacity} churn=20000 max_absent_probes={max_absent_probes}");
}

#[test]
fn actual_backing_authority_busy_mutation_and_freed_key_refuse() {
    let dict = rt_dict_new(0);
    let key = text("key-with-unique-storage");
    assert!(rt_dict_set(dict, key, RuntimeValue::from_int(1)));
    let (owner, epoch) = view(dict);
    let index = first_live(dict, owner, epoch);
    let ptr = dict.as_heap_ptr() as *mut RuntimeDict;
    unsafe {
        let capacity = (*ptr).capacity;
        (*ptr).capacity += 1;
        assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
        (*ptr).capacity = capacity;
        let data = (*ptr).data;
        (*ptr).data = 0x1000usize as *mut RuntimeValue;
        assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
        (*ptr).data = data;
    }
    {
        let _mutation = mutation(ptr);
        assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
    }
    assert_eq!(rt_dict_scope_read_meta_v1(dict, owner, epoch, 0, READ_BOUND), -1);
    let (owner, epoch) = view(dict);
    assert_eq!(slot(dict, owner, epoch, index, 0, 0), 1);
    assert_eq!(super::super::collections::rt_string_free(key), 1);
    assert_eq!(slot(dict, owner, epoch, index, 0, 0), -1);
    rt_dict_free(dict);
}

#[test]
fn realistic_scope_reads_allocate_nothing_and_do_not_wait() {
    let dict = rt_dict_new(0);
    for id in 0..4096 {
        assert!(rt_dict_set(
            dict,
            text(&format!("realistic-binding-{id}")),
            RuntimeValue::from_int(id)
        ));
    }
    assert!(rt_dict_set(dict, text("café猫"), RuntimeValue::from_int(i64::MAX)));
    let (owner, epoch) = view(dict);
    let index = first_live(dict, owner, epoch);
    {
        let _locked = registry().lock().unwrap();
        assert_eq!(rt_dict_scope_read_owner_v1(dict, READ_BOUND), -1);
    }
    let start = std::time::Instant::now();
    COUNT.with(|count| count.set(Some(0)));
    let mut sum = 0;
    for _ in 0..100_000 {
        sum += std::hint::black_box(slot(dict, owner, epoch, index, 0, 0));
    }
    let allocations = COUNT.with(|count| count.replace(None).unwrap());
    let elapsed = start.elapsed();
    assert_eq!(sum, 100_000);
    assert_eq!(allocations, 0);
    assert!(elapsed < std::time::Duration::from_secs(10));
    println!(
        "HOSTED_RUST_SCOPE_READ allocations={allocations} reads=100000 scope=4097 elapsed_us={} bound={READ_BOUND}",
        elapsed.as_micros()
    );
    rt_dict_free(dict);
}

#[test]
fn z_large_scope_construction_churn_registry_footprint_and_rss() {
    fn registry_bytes() -> (usize, usize) {
        let registry = registry().lock().unwrap();
        (
            registry.slots.capacity() * std::mem::size_of::<Entry>()
                + registry.dictionaries.capacity() * std::mem::size_of::<Descriptor>()
                + registry.free_descriptors.capacity() * std::mem::size_of::<usize>(),
            registry.slots.len(),
        )
    }
    let (before_bytes, _) = registry_bytes();
    let start = std::time::Instant::now();
    let dict = rt_dict_new(0);
    for id in 0..65_536 {
        assert!(rt_dict_set(
            dict,
            text(&format!("large-scope-binding-{id}")),
            RuntimeValue::from_int(id)
        ));
    }
    let construction = start.elapsed();
    let key = text("mutation-churn-binding");
    assert!(rt_dict_set(dict, key, RuntimeValue::from_int(1)));
    let start = std::time::Instant::now();
    for id in 0..100_000 {
        assert!(rt_dict_set(dict, key, RuntimeValue::from_int(id)));
    }
    let churn = start.elapsed();
    let (owner, epoch) = view(dict);
    let capacity = rt_dict_scope_read_meta_v1(dict, owner, epoch, 3, READ_BOUND);
    let mut occupied = 0;
    let start = std::time::Instant::now();
    COUNT.with(|count| count.set(Some(0)));
    for index in 0..capacity {
        let status = slot(dict, owner, epoch, index, 0, 0);
        assert!((0..=1).contains(&status));
        occupied += status;
    }
    let allocations = COUNT.with(|count| count.replace(None).unwrap());
    let scan = start.elapsed();
    assert_eq!(occupied, 65_537);
    assert_eq!(allocations, 0);
    let (registry_bytes, registry_slots) = registry_bytes();
    let mut max_rss_kib = -1;
    #[cfg(target_os = "linux")]
    unsafe {
        let mut usage: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut usage) == 0 {
            max_rss_kib = usage.ru_maxrss;
        }
    }
    println!("HOSTED_RUST_LARGE_SCOPE bindings=65537 construction_us={} replacements=100000 replacement_us={} scan_slots={capacity} scan_us={} allocations={allocations} registry_slots={registry_slots} registry_bytes={registry_bytes} registry_growth_bytes={} entry_stride={} max_rss_kib={max_rss_kib}", construction.as_micros(), churn.as_micros(), scan.as_micros(), registry_bytes - before_bytes, std::mem::size_of::<Entry>());
    rt_dict_free(dict);
}
