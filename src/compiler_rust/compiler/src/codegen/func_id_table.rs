//! Function-name -> `FuncId` table with a module-qualified suffix index.
//!
//! `CodegenBackend::func_ids` maps every declared symbol (raw names, mangled
//! `module__name` forms, runtime imports, ...) to its Cranelift `FuncId`. The
//! method-call lowering resolves a bare or dot-qualified callee name to a
//! unique "module-qualified" entry: a key of the form `<prefix>__<tail>` whose
//! `<tail>` equals the probed name's own tail. Before this type existed that
//! lookup walked the whole map once per probe (two probes per method call),
//! so a module with F functions and C call sites cost O(F * C) string
//! comparisons -- about 7,200 functions for the native-build CLI, which made
//! `resolve_unique_module_qualified_func` one of the hottest frames of the
//! seed JIT (macOS `sample` of the combined-seed hello native-build,
//! 2026-10-30: 488 samples here vs 1054 in `implicit_local_param_slots` in
//! one sample, 883 vs 2090 in a later one).
//!
//! `FuncIdTable` keeps the `BTreeMap` (read access is unchanged through
//! `Deref`) and maintains, on every insert, an index from each tail a key can
//! be probed by to the keys that carry it. A probe then inspects only the
//! handful of keys sharing its tail. The index is derived purely from the key
//! text, so an overwriting insert of an existing key (same key, new id) needs
//! no index change: lookups read the current id from the map.
//!
//! Semantics are intentionally bit-for-bit those of the previous linear scan
//! (`reference_resolve` in the tests below is that scan, kept as the oracle).

use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use cranelift_module::FuncId;

/// `func_ids` map plus the tail index. Mutation goes through `insert` /
/// `or_insert` only, so the index can never fall out of sync with the map.
/// There is deliberately no `DerefMut`.
#[derive(Debug, Default, Clone)]
pub struct FuncIdTable {
    map: BTreeMap<String, FuncId>,
    /// tail -> keys of `map` that match a probe with that tail. A key appears
    /// once per tail it qualifies for (see `qualified_tails`), never twice
    /// under the same tail.
    by_tail: HashMap<String, Vec<String>>,
}

impl Deref for FuncIdTable {
    type Target = BTreeMap<String, FuncId>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl From<BTreeMap<String, FuncId>> for FuncIdTable {
    fn from(map: BTreeMap<String, FuncId>) -> Self {
        let mut table = FuncIdTable::new();
        for (key, id) in map {
            table.insert(key, id);
        }
        table
    }
}

impl FuncIdTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Same contract as `BTreeMap::insert`: returns the previous id when the
    /// key was already present (the key's index entries are already there and
    /// unchanged, since they depend only on the key text).
    pub fn insert(&mut self, key: String, id: FuncId) -> Option<FuncId> {
        if let Some(slot) = self.map.get_mut(&key) {
            return Some(std::mem::replace(slot, id));
        }
        for tail in qualified_tails(&key) {
            self.by_tail.entry(tail.to_string()).or_default().push(key.clone());
        }
        self.map.insert(key, id);
        None
    }

    /// Same contract as `BTreeMap::entry(key).or_insert(id)`: keeps an
    /// existing mapping, otherwise inserts `id`. Returns the mapping in effect.
    pub fn or_insert(&mut self, key: String, id: FuncId) -> FuncId {
        if let Some(existing) = self.map.get(&key) {
            return *existing;
        }
        self.insert(key, id);
        id
    }

    /// Resolve `name` to the unique module-qualified entry whose tail equals
    /// `name`'s tail, or `None` when there is no such entry or more than one
    /// distinct `FuncId` qualifies.
    ///
    /// Exactly the former linear scan in
    /// `codegen::instr::closures_structs::resolve_unique_module_qualified_func`:
    /// a key `k` matches when `k.strip_suffix("__<tail>")` leaves a non-empty
    /// prefix that does not end in `_` (the mangling boundary: a private
    /// helper `_index_of` mangles to `<module>___index_of`, which must not
    /// bind the method `index_of`), and keys carrying a flatten-owner identity
    /// (`__spl_flat_<owner>__Type.method`) never match by suffix.
    pub fn resolve_unique_module_qualified(&self, name: &str) -> Option<FuncId> {
        let sanitized = name.replace('.', "_dot_");
        let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
        let keys = self.by_tail.get(tail)?;
        let mut unique: Option<FuncId> = None;
        for key in keys {
            if key.starts_with(crate::interpreter::FLATTEN_OWNER_SYMBOL_PREFIX) {
                continue;
            }
            // Keys are never removed, so this is always `Some`; stay total.
            let Some(&id) = self.map.get(key) else { continue };
            match unique {
                None => unique = Some(id),
                Some(seen) if seen == id => {}
                Some(_) => return None,
            }
        }
        unique
    }

    /// Number of keys a probe for `name` has to inspect (the index bucket
    /// size). Test-only observability for the scaling assertions.
    #[cfg(test)]
    pub fn candidates_examined(&self, name: &str) -> usize {
        let sanitized = name.replace('.', "_dot_");
        let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
        self.by_tail.get(tail).map_or(0, Vec::len)
    }
}

/// Every `tail` such that `key == prefix + "__" + tail` with a non-empty
/// `prefix` that does not end in `_`.
///
/// Such a split starts exactly at the first two underscores of each maximal
/// underscore run of length >= 2 that is preceded by a non-underscore byte, so
/// a key yields one tail per such run (`a__b__c` -> `b__c`, `c`;
/// `m___x` -> `_x`; `__x` -> nothing, the prefix would be empty). The split
/// bytes are ASCII `_`, so every slice boundary is a char boundary.
pub fn qualified_tails(key: &str) -> impl Iterator<Item = &str> + '_ {
    let bytes = key.as_bytes();
    (1..bytes.len().saturating_sub(1))
        .filter(move |&i| bytes[i] == b'_' && bytes[i + 1] == b'_' && bytes[i - 1] != b'_')
        .map(move |i| &key[i + 2..])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The previous implementation, verbatim up to the map type, kept as the
    /// oracle the indexed lookup must agree with.
    fn reference_resolve(func_ids: &BTreeMap<String, FuncId>, name: &str) -> Option<FuncId> {
        let sanitized = name.replace('.', "_dot_");
        let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
        let suffix = format!("__{}", tail);
        let mut ids: Vec<FuncId> = Vec::new();
        for (candidate, id) in func_ids.iter() {
            if candidate
                .strip_suffix(&suffix)
                .is_some_and(|prefix| !prefix.is_empty() && !prefix.ends_with('_'))
                && !candidate.starts_with(crate::interpreter::FLATTEN_OWNER_SYMBOL_PREFIX)
                && !ids.contains(id)
            {
                ids.push(*id);
            }
        }
        if ids.len() == 1 {
            ids.first().copied()
        } else {
            None
        }
    }

    fn fid(n: u32) -> FuncId {
        FuncId::from_u32(n)
    }

    fn table(entries: &[(&str, u32)]) -> (FuncIdTable, BTreeMap<String, FuncId>) {
        let mut t = FuncIdTable::new();
        let mut m = BTreeMap::new();
        for (k, id) in entries {
            t.insert(k.to_string(), fid(*id));
            m.insert(k.to_string(), fid(*id));
        }
        (t, m)
    }

    fn assert_agrees(t: &FuncIdTable, m: &BTreeMap<String, FuncId>, probe: &str) {
        assert_eq!(
            t.resolve_unique_module_qualified(probe),
            reference_resolve(m, probe),
            "probe {probe:?} over keys {:?}",
            m.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn qualified_tails_enumerates_one_split_per_underscore_run() {
        let tails = |k: &str| qualified_tails(k).map(str::to_string).collect::<Vec<_>>();
        assert_eq!(tails("mod__f"), vec!["f"]);
        assert_eq!(tails("a__b__c"), vec!["b__c", "c"]);
        assert_eq!(tails("mod___index_of"), vec!["_index_of"]);
        assert_eq!(tails("mod____x"), vec!["__x"]);
        assert_eq!(tails("__x"), Vec::<String>::new());
        assert_eq!(tails("x__"), vec![""]);
        assert_eq!(tails("x"), Vec::<String>::new());
        assert_eq!(tails(""), Vec::<String>::new());
        assert_eq!(tails("_"), Vec::<String>::new());
        assert_eq!(tails("__"), Vec::<String>::new());
        assert_eq!(tails("a_b"), Vec::<String>::new());
        assert_eq!(tails("m\u{e9}__caf\u{e9}"), vec!["caf\u{e9}"]);
    }

    #[test]
    fn resolves_unique_and_refuses_ambiguous_exactly_like_the_scan() {
        let (t, m) = table(&[
            ("alpha__index_of", 1),
            ("beta__index_of", 1),   // same id twice: still unique
            ("gamma___index_of", 2), // private helper: `_index_of`, not `index_of`
            ("Point_dot_len", 3),
            ("geo__Point_dot_len", 3),
            ("__spl_flat_owner__Point_dot_len", 4), // flatten owner: never by suffix
            ("util__to_string", 5),
            ("fmt__to_string", 6), // ambiguous with the previous
            ("__to_string", 7),    // empty prefix: not module-qualified
            ("x__", 8),
        ]);
        assert_eq!(t.resolve_unique_module_qualified("index_of"), Some(fid(1)));
        assert_eq!(t.resolve_unique_module_qualified("_index_of"), Some(fid(2)));
        assert_eq!(t.resolve_unique_module_qualified("Point.len"), Some(fid(3)));
        assert_eq!(t.resolve_unique_module_qualified("geo.Point.len"), None);
        assert_eq!(t.resolve_unique_module_qualified("to_string"), None);
        assert_eq!(t.resolve_unique_module_qualified("missing"), None);
        assert_eq!(t.resolve_unique_module_qualified("x__"), Some(fid(8)));
        for probe in [
            "index_of",
            "_index_of",
            "Point.len",
            "Point_dot_len",
            "geo.Point.len",
            "to_string",
            "missing",
            "x__",
            "",
            "__",
            "_",
            "a__index_of",
            "spl_flat_owner__Point.len",
        ] {
            assert_agrees(&t, &m, probe);
        }
    }

    #[test]
    fn overwriting_insert_and_or_insert_match_btreemap_contracts() {
        let mut t = FuncIdTable::new();
        let mut m = BTreeMap::new();
        assert_eq!(t.insert("m__f".into(), fid(1)), None);
        assert_eq!(m.insert("m__f".to_string(), fid(1)), None);
        assert_eq!(t.or_insert("m__f".into(), fid(9)), fid(1));
        assert_eq!(*m.entry("m__f".to_string()).or_insert(fid(9)), fid(1));
        assert_eq!(t.or_insert("n__g".into(), fid(2)), fid(2));
        assert_eq!(*m.entry("n__g".to_string()).or_insert(fid(2)), fid(2));
        assert_eq!(t.insert("m__f".into(), fid(3)), Some(fid(1)));
        assert_eq!(m.insert("m__f".to_string(), fid(3)), Some(fid(1)));
        assert_eq!(*t, m);
        assert_eq!(t.resolve_unique_module_qualified("f"), Some(fid(3)));
        // A key is indexed once per tail even after being re-inserted.
        assert_eq!(t.candidates_examined("f"), 1);
        assert_agrees(&t, &m, "f");
        assert_agrees(&t, &m, "g");
    }

    /// Small deterministic xorshift so the test needs no extra dependency and
    /// a failure reproduces from the printed seed.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Alphabet chosen so `__` runs, `_dot_`, `.`, leading/trailing
    /// underscores and shared tails are all frequent.
    fn random_name(rng: &mut Rng) -> String {
        const PIECES: &[&str] = &["a", "b", "c", "_", "__", "___", ".", "_dot_", "x", "index_of"];
        let len = 1 + rng.below(5);
        let mut s = String::new();
        for _ in 0..len {
            s.push_str(PIECES[rng.below(PIECES.len())]);
        }
        if rng.below(12) == 0 {
            s = format!("{}{}", crate::interpreter::FLATTEN_OWNER_SYMBOL_PREFIX, s);
        }
        s
    }

    #[test]
    fn indexed_lookup_agrees_with_linear_scan_on_random_tables() {
        for seed in 1..=40u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut t = FuncIdTable::new();
            let mut m = BTreeMap::new();
            let mut probes: Vec<String> = Vec::new();
            for step in 0..120 {
                let key = random_name(&mut rng);
                // Few distinct ids so same-id duplicates (still unique) and
                // different-id duplicates (ambiguous) both occur often.
                let id = fid(rng.below(4) as u32);
                if rng.below(4) == 0 {
                    assert_eq!(
                        t.or_insert(key.clone(), id),
                        *m.entry(key.clone()).or_insert(id),
                        "seed {seed} step {step}"
                    );
                } else {
                    assert_eq!(
                        t.insert(key.clone(), id),
                        m.insert(key.clone(), id),
                        "seed {seed} step {step}"
                    );
                }
                assert_eq!(*t, m, "seed {seed} step {step}");
                probes.push(key);
                // Check after EVERY mutation, over keys, their tails, and
                // unrelated names, so an index that lags the map is caught.
                for probe in probes
                    .iter()
                    .take(16)
                    .cloned()
                    .chain((0..8).map(|_| random_name(&mut rng)))
                {
                    assert_agrees(&t, &m, &probe);
                    for tail in qualified_tails(&probe) {
                        assert_agrees(&t, &m, tail);
                    }
                }
            }
            assert_eq!(t.len(), m.len());
            for probe in &probes {
                assert_agrees(&t, &m, probe);
            }
        }
    }

    fn big_table(n: usize) -> (FuncIdTable, BTreeMap<String, FuncId>) {
        let mut t = FuncIdTable::new();
        let mut m = BTreeMap::new();
        for i in 0..n {
            // Distinct tails plus a mangled and a raw form each, as the real
            // table holds (`module__name` and `name`).
            for key in [
                format!("mod{}__fn_{i}", i % 97),
                format!("fn_{i}"),
                format!("mod{}__Type{i}_dot_m", i % 97),
            ] {
                t.insert(key.clone(), fid(i as u32));
                m.insert(key, fid(i as u32));
            }
        }
        (t, m)
    }

    #[test]
    fn work_per_probe_is_independent_of_table_size() {
        let (small, _) = big_table(1_000);
        let (large, _) = big_table(16_000);
        for probe in ["fn_7", "Type7.m", "mod7__fn_7", "nothing_here"] {
            let a = small.candidates_examined(probe);
            let b = large.candidates_examined(probe);
            assert_eq!(a, b, "probe {probe:?}: bucket grew with the table ({a} vs {b})");
            assert!(a <= 1, "probe {probe:?} inspects {a} keys");
            assert_eq!(
                small.resolve_unique_module_qualified(probe),
                large.resolve_unique_module_qualified(probe)
            );
        }
        // The old scan inspected every key: 3 per function.
        assert_eq!(large.len(), 48_000);
    }

    /// Wall-clock comparison for the report; ignored by default because the
    /// CI hosts are loaded and absolute timings are not stable there.
    /// `cargo test -p simple-compiler --lib func_id_table -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn timing_indexed_vs_linear_scan() {
        use std::time::Instant;
        for n in [1_000usize, 4_000, 8_000] {
            let (t, m) = big_table(n);
            let probes: Vec<String> = (0..2_000).map(|i| format!("Type{}.m", (i * 7919) % n)).collect();
            let start = Instant::now();
            let mut hits = 0usize;
            for p in &probes {
                hits += reference_resolve(&m, p).is_some() as usize;
            }
            let linear = start.elapsed();
            let start = Instant::now();
            let mut hits2 = 0usize;
            for p in &probes {
                hits2 += t.resolve_unique_module_qualified(p).is_some() as usize;
            }
            let indexed = start.elapsed();
            assert_eq!(hits, hits2);
            eprintln!(
                "functions={n:>6} keys={:>6} probes={} linear={:>10.3?} indexed={:>10.3?} ratio={:.0}x",
                m.len(),
                probes.len(),
                linear,
                indexed,
                linear.as_secs_f64() / indexed.as_secs_f64().max(1e-9)
            );
        }
    }
}
