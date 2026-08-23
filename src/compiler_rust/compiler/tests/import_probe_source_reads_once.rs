// Mechanism-pinned reproduce test for the import-resolution probe re-read.
//
// Pre-fix, `sibling_might_define_requested_names` and `file_plausibly_provides_names`
// each called `fs::read_to_string` on every visit. Because those probes re-run once
// per IMPORTING module, a single trivial `bin/simple lint` issued 3,819 successful
// `openat` calls over 423 distinct `.spl` files — `10.frontend/core/ast.spl` alone
// 866 times, 67.7 MB read for 5.1 MB of distinct content (13.3x amplification).
// That redundant read is ~37s of the ~44s a lint costs, and it dominates every
// interpreted entry point (`lint`, `test`, `run`), not just lint.
//
// Pinned by COUNT rather than by wall clock: the box this runs on carries load
// averages in the 40s, so a time budget would be noise. N visits to the same path
// must produce exactly ONE read.
//
// Fails pre-fix: `probe_source_cached` did not exist, and the counters it bumps
// were absent, so there was no path by which a second visit could avoid a read.

use simple_compiler::interpreter::{clear_probe_source_cache, probe_source_cached};
use simple_compiler::perf_counters::{self, PROBE_SOURCE_HITS, PROBE_SOURCE_READS};
use std::sync::atomic::Ordering;

#[test]
fn repeated_probe_of_the_same_path_reads_the_file_exactly_once() {
    perf_counters::set_enabled(true);
    clear_probe_source_cache();
    PROBE_SOURCE_READS.store(0, Ordering::Relaxed);
    PROBE_SOURCE_HITS.store(0, Ordering::Relaxed);

    let dir = std::env::temp_dir().join(format!("probe-memo-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let a = dir.join("a.spl");
    let b = dir.join("b.spl");
    std::fs::write(&a, "pub fn alpha() -> i64:\n    1\n").expect("write a");
    std::fs::write(&b, "pub fn beta() -> i64:\n    2\n").expect("write b");

    // 50 visits across 2 distinct paths, the shape a real import graph produces.
    for _ in 0..25 {
        let sa = probe_source_cached(&a, 1 << 20).expect("a readable");
        let sb = probe_source_cached(&b, 1 << 20).expect("b readable");
        // Memoization must not corrupt the content the probes scan.
        assert!(sa.contains("alpha"), "cached content for a.spl is wrong");
        assert!(sb.contains("beta"), "cached content for b.spl is wrong");
    }

    let reads = PROBE_SOURCE_READS.load(Ordering::Relaxed);
    let hits = PROBE_SOURCE_HITS.load(Ordering::Relaxed);
    assert_eq!(reads, 2, "expected one read per DISTINCT path, got {reads}");
    assert_eq!(hits, 48, "expected every repeat visit to be a memo hit, got {hits}");

    // The size cap still classifies identically, and a rejection is memoized too
    // (pre-fix it re-`stat`ed and re-read on every visit).
    let before = PROBE_SOURCE_READS.load(Ordering::Relaxed);
    let big = dir.join("big.spl");
    std::fs::write(&big, "x".repeat(4096)).expect("write big");
    for _ in 0..10 {
        assert!(
            probe_source_cached(&big, 16).is_none(),
            "a file over the probe size cap must stay ineligible"
        );
    }
    assert_eq!(
        PROBE_SOURCE_READS.load(Ordering::Relaxed) - before,
        1,
        "an over-cap rejection must be memoized, not recomputed per visit"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
