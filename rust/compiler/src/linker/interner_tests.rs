use super::*;

#[test]
fn test_symbol_interner_basic() {
    let mut interner = SymbolInterner::new();

    let key1 = interner.intern("main");
    let key2 = interner.intern("foo");
    let key3 = interner.intern("main"); // Same as key1

    assert_eq!(key1, key3);
    assert_ne!(key1, key2);

    assert_eq!(interner.resolve(key1), "main");
    assert_eq!(interner.resolve(key2), "foo");
}

#[test]
fn test_symbol_interner_section_value() {
    let mut interner = SymbolInterner::new();

    let key = interner.intern("main");
    interner.set_section(key, 1);
    interner.set_value(key, 0x1000);

    assert_eq!(interner.get_section(key), Some(1));
    assert_eq!(interner.get_value(key), Some(0x1000));
}

#[test]
fn test_shared_interner_thread_safe() {
    use std::thread;

    let interner = SharedSymbolInterner::new();

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let interner = interner.clone();
            thread::spawn(move || {
                for j in 0..100 {
                    let s = format!("symbol_{}_{}", i, j);
                    interner.intern(&s);
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(interner.len(), 400);
}

#[test]
fn test_interned_symbol_table() {
    let mut table = InternedSymbolTable::new();

    let key1 = table.add_symbol(
        "main",
        SymbolInfo {
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 1,
            value: 0x1000,
            size: 100,
        },
    );

    let key2 = table.add_symbol(
        "helper",
        SymbolInfo {
            binding: SymbolBinding::Local,
            sym_type: SymbolType::Function,
            section_index: 1,
            value: 0x1100,
            size: 50,
        },
    );

    assert_eq!(table.len(), 2);
    assert!(table.contains("main"));
    assert!(table.contains("helper"));

    let (_, info) = table.lookup("main").unwrap();
    assert_eq!(info.value, 0x1000);

    // Check globals iterator
    let globals: Vec<_> = table.globals().collect();
    assert_eq!(globals.len(), 1);
    assert_eq!(table.resolve(globals[0].0), "main");
}

#[test]
fn test_common_symbols() {
    let mut interner = SymbolInterner::new();
    let common = CommonSymbols::new(&mut interner);

    assert_eq!(interner.resolve(common.main), "main");
    assert_eq!(interner.resolve(common.text), ".text");
    assert_eq!(interner.resolve(common.start), "_start");
}

#[test]
fn test_o1_comparison() {
    let mut interner = SymbolInterner::new();

    // Intern long symbol names
    let long1 = "very_long_symbol_name_that_appears_many_times_in_linking";
    let long2 = "another_very_long_symbol_name_that_is_completely_different";

    let key1a = interner.intern(long1);
    let key1b = interner.intern(long1);
    let key2 = interner.intern(long2);

    // Comparison is O(1) - just comparing integers
    assert_eq!(key1a, key1b);
    assert_ne!(key1a, key2);
}

#[test]
fn test_symbol_table_iteration_order() {
    let mut table = InternedSymbolTable::new();

    table.add_symbol(
        "first",
        SymbolInfo {
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 1,
            value: 0,
            size: 0,
        },
    );

    table.add_symbol(
        "second",
        SymbolInfo {
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 1,
            value: 0,
            size: 0,
        },
    );

    table.add_symbol(
        "third",
        SymbolInfo {
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 1,
            value: 0,
            size: 0,
        },
    );

    let names: Vec<_> = table.iter().map(|(_, name, _)| name).collect();
    assert_eq!(names, vec!["first", "second", "third"]);
}

// Hash precomputation tests (#815)

#[test]
fn test_precomputed_hash() {
    let hash1 = PrecomputedHash::compute("hello");
    let hash2 = PrecomputedHash::compute("hello");
    let hash3 = PrecomputedHash::compute("world");

    // Same string = same hash
    assert_eq!(hash1, hash2);
    // Different strings = different hashes (with high probability)
    assert_ne!(hash1, hash3);
    // Hash value should be non-zero for non-empty strings
    assert_ne!(hash1.value(), 0);
}

#[test]
fn test_hashed_symbol() {
    let mut interner = SymbolInterner::new();
    let key = interner.intern("test");
    let hash = PrecomputedHash::compute("test");
    let symbol = HashedSymbol::new(key, hash);

    assert_eq!(symbol.key, key);
    assert_eq!(symbol.hash, hash);
}

#[test]
fn test_prehashed_table() {
    let mut table = PrehashedTable::<i32>::new();
    assert!(table.is_empty());

    let mut interner = HashedInterner::new();
    let sym1 = interner.intern("foo");
    let sym2 = interner.intern("bar");

    table.insert(sym1.clone(), 100);
    table.insert(sym2.clone(), 200);

    assert_eq!(table.len(), 2);
    assert_eq!(table.get(&sym1), Some(&100));
    assert_eq!(table.get(&sym2), Some(&200));
    assert!(table.contains(&sym1));
}

#[test]
fn test_prehashed_table_update() {
    let mut table = PrehashedTable::<i32>::new();
    let mut interner = HashedInterner::new();
    let sym = interner.intern("key");

    assert!(table.insert(sym.clone(), 100).is_none());
    assert_eq!(table.insert(sym.clone(), 200), Some(100));
    assert_eq!(table.get(&sym), Some(&200));
}

#[test]
fn test_hashed_interner() {
    let mut interner = HashedInterner::new();

    let sym1 = interner.intern("hello");
    let sym2 = interner.intern("world");
    let sym3 = interner.intern("hello"); // Same as sym1

    assert_eq!(sym1.key, sym3.key);
    assert_eq!(sym1.hash, sym3.hash);
    assert_ne!(sym1.key, sym2.key);

    assert_eq!(interner.len(), 2);
    assert_eq!(interner.resolve(sym1.key), "hello");
    assert_eq!(interner.resolve(sym2.key), "world");
}

#[test]
fn test_hashed_interner_get() {
    let mut interner = HashedInterner::new();

    assert!(interner.get("missing").is_none());

    let sym = interner.intern("present");
    let retrieved = interner.get("present").unwrap();

    assert_eq!(sym.key, retrieved.key);
    assert_eq!(sym.hash, retrieved.hash);
}

#[test]
fn test_prehashed_table_iteration() {
    let mut table = PrehashedTable::<i32>::new();
    let mut interner = HashedInterner::new();

    table.insert(interner.intern("a"), 1);
    table.insert(interner.intern("b"), 2);
    table.insert(interner.intern("c"), 3);

    let mut values: Vec<i32> = table.iter().map(|(_, v)| *v).collect();
    values.sort();
    assert_eq!(values, vec![1, 2, 3]);
}

#[test]
fn test_hash_precomputation_performance() {
    // Test that hash computation is consistent
    let mut interner = HashedInterner::new();

    // Intern many symbols
    for i in 0..100 {
        let name = format!("symbol_{}", i);
        let sym = interner.intern(&name);

        // Hash should be cached
        let cached_hash = interner.get_hash(sym.key).unwrap();
        assert_eq!(sym.hash, cached_hash);
    }

    assert_eq!(interner.len(), 100);
}
