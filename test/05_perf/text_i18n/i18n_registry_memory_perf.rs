use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

struct CountingAllocator;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
            let live = LIVE.fetch_add(layout.size(), Ordering::Relaxed) + layout.size();
            PEAK.fetch_max(live, Ordering::Relaxed);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

pub mod extractor {
    use std::collections::HashMap;

    pub struct I18nString {
        pub name: String,
        pub default_text: String,
        pub template_vars: Vec<String>,
        pub source_file: std::path::PathBuf,
        pub line: usize,
        pub scope: String,
    }

    #[derive(Default)]
    pub struct ExtractionResult {
        pub strings: HashMap<String, I18nString>,
    }
}

#[path = "../../../src/compiler_rust/compiler/src/i18n/locale.rs"]
pub mod locale;

#[path = "../../../src/compiler_rust/compiler/src/i18n/registry.rs"]
pub mod registry;

fn rss_kib() -> usize {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status.lines().find_map(|line| {
                line.strip_prefix("VmHWM:")?
                    .split_whitespace()
                    .next()?
                    .parse().ok()
            })
        })
        .unwrap_or(0)
}

fn main() {
    const MESSAGES: usize = 4096;
    const LOOKUPS: usize = 100_000;
    registry::clear();

    let baseline_live = LIVE.load(Ordering::Relaxed);
    let strings = (0..MESSAGES)
        .map(|i| {
            (
                format!("Message_{i:04}_"),
                format!("Localized value {i:04} 한국어 العربية emoji 👩‍💻"),
            )
        })
        .collect::<HashMap<_, _>>();
    registry::load_strings("ko-KR", strings);
    registry::set_locale("ko-KR");
    let catalog_live = LIVE.load(Ordering::Relaxed) - baseline_live;
    let keys = (0..MESSAGES)
        .map(|i| format!("Message_{i:04}_"))
        .collect::<Vec<_>>();

    let allocs_before = ALLOCS.load(Ordering::Relaxed);
    let start = Instant::now();
    let mut bytes = 0usize;
    for i in 0..LOOKUPS {
        bytes += black_box(registry::lookup(&keys[i % MESSAGES]).unwrap()).len();
    }
    let elapsed = start.elapsed();
    let lookup_allocs = ALLOCS.load(Ordering::Relaxed) - allocs_before;
    black_box(bytes);

    registry::clear();
    drop(keys);
    let retained_after_clear = LIVE.load(Ordering::Relaxed).saturating_sub(baseline_live);

    println!(
        "messages={MESSAGES} lookups={LOOKUPS} catalog_live_bytes={catalog_live} \
lookup_allocations={lookup_allocs} allocations_per_lookup={:.3} \
ns_per_lookup={:.2} retained_after_clear_bytes={retained_after_clear} \
peak_live_bytes={} vmhwm_kib={}",
        lookup_allocs as f64 / LOOKUPS as f64,
        elapsed.as_nanos() as f64 / LOOKUPS as f64,
        PEAK.load(Ordering::Relaxed),
        rss_kib(),
    );

    assert_eq!(lookup_allocs, LOOKUPS * 2);
    assert!(catalog_live > retained_after_clear);
    assert!(retained_after_clear <= 1024);
}
