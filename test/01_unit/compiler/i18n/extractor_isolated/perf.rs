use simple_i18n_extractor_isolated::extractor::I18nExtractor;
use simple_parser::Parser;
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

struct CountingAllocator;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
            ALLOCATED.fetch_add(layout.size(), Ordering::Relaxed);
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

fn rss_hwm_kib() -> usize {
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
    let mut source = String::from("fn catalog():\n");
    for i in 0..MESSAGES {
        source.push_str(&format!(
            "    print(Message_{i:04}_\"Value {i:04} 한국어 العربية 👩‍💻\")\n"
        ));
    }
    let mut parser = Parser::new(&source);
    let module = parser.parse().expect("generated extraction fixture must parse");

    let baseline_live = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline_live, Ordering::Relaxed);
    let allocs_before = ALLOCS.load(Ordering::Relaxed);
    let bytes_before = ALLOCATED.load(Ordering::Relaxed);
    let started = Instant::now();
    let mut extractor = I18nExtractor::new();
    extractor.extract_module(&module, PathBuf::from("catalog.spl"));
    let result = black_box(extractor.finish());
    let elapsed = started.elapsed();

    let allocations = ALLOCS.load(Ordering::Relaxed) - allocs_before;
    let allocated_bytes = ALLOCATED.load(Ordering::Relaxed) - bytes_before;
    let result_live_bytes = LIVE.load(Ordering::Relaxed) - baseline_live;
    let peak_above_fixture = PEAK.load(Ordering::Relaxed) - baseline_live;
    assert_eq!(result.strings.len(), MESSAGES);
    assert!(result.warnings.is_empty());
    black_box(&result.strings);
    drop(result);
    let retained = LIVE.load(Ordering::Relaxed) - baseline_live;

    println!(
        "messages={MESSAGES} source_bytes={} ns_total={} ns_per_message={:.2} \
allocations={allocations} allocated_bytes={allocated_bytes} \
result_live_bytes={result_live_bytes} peak_above_fixture_bytes={peak_above_fixture} \
retained_after_drop_bytes={retained} vmhwm_kib={}",
        source.len(),
        elapsed.as_nanos(),
        elapsed.as_nanos() as f64 / MESSAGES as f64,
        rss_hwm_kib(),
    );

    assert_eq!(retained, 0);
}
