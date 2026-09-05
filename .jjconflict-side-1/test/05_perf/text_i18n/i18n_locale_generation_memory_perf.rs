use std::alloc::{GlobalAlloc, Layout, System};
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
    let mut catalog = locale::LocaleFile::new("ko-KR");
    for i in 0..MESSAGES {
        catalog.add_string(
            &format!("Message_{i:04}_"),
            &format!("Localized value {i:04} 한국어 العربية emoji 👩‍💻"),
        );
    }

    let baseline_live = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline_live, Ordering::Relaxed);
    let allocations_before = ALLOCS.load(Ordering::Relaxed);
    let start = Instant::now();
    let source = black_box(catalog.to_simple_source());
    let elapsed = start.elapsed();
    let allocations = ALLOCS.load(Ordering::Relaxed) - allocations_before;
    let generated_live_bytes = LIVE.load(Ordering::Relaxed) - baseline_live;
    let transient_peak_bytes = PEAK.load(Ordering::Relaxed) - baseline_live;
    let output_bytes = source.len();
    black_box(source.as_bytes());
    drop(source);
    let retained_after_output_drop = LIVE.load(Ordering::Relaxed) - baseline_live;

    println!(
        "messages={MESSAGES} output_bytes={output_bytes} allocations={allocations} \
ns_total={} ns_per_message={:.2} generated_live_bytes={generated_live_bytes} \
transient_peak_bytes={transient_peak_bytes} retained_after_output_drop_bytes={} \
vmhwm_kib={}",
        elapsed.as_nanos(),
        elapsed.as_nanos() as f64 / MESSAGES as f64,
        retained_after_output_drop,
        rss_kib(),
    );

    assert_eq!(retained_after_output_drop, 0);
    assert!(generated_live_bytes >= output_bytes);
}
