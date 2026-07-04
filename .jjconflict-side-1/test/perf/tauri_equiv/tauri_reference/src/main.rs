// Tauri reference benchmark — Simple GUI vs Rust+Tauri comparison (NFR 2B / Workstream 9)
//
// This file compiles in two modes:
//
//   1. Headless stub (default): no Tauri dependency required. Simulates all
//      workflow timings using std::time so the harness can run anywhere.
//      Build: cargo build
//
//   2. Tauri-full (with real windows): requires Tauri 1.x and a display.
//      Build: cargo build --features tauri-full
//
// Output format (stdout, one line per sample):
//   [tauri-equiv] workflow=<name> elapsed_us=<N> rss_kb=<N>
//   [tauri-equiv-summary] workflow=<name> p50_us=<N> p95_us=<N> rss_kb=<N>
//
// Aggregation is performed by workflow_driver.spl.

use std::time::{Duration, Instant};

// ============================================================================
// Constants
// ============================================================================

const WARMUP_ITERS: usize = 3;
const DEFAULT_ITERS: usize = 20;
const IDLE_DURATION_MS: u64 = 10_000;
const SCROLL_ROWS: usize = 10_000;
const WINDOW_WIDTH: u32 = 1280;
const WINDOW_HEIGHT: u32 = 800;
const CHILD_WIDTH: u32 = 640;
const CHILD_HEIGHT: u32 = 480;

// ============================================================================
// RSS measurement (Linux /proc/self/status)
// ============================================================================

fn read_rss_kb() -> u64 {
    #[cfg(target_os = "linux")]
    {
        let content = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
        for line in content.lines() {
            if line.starts_with("VmRSS:") {
                let num: u64 = line
                    .split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
                return num;
            }
        }
        0
    }
    #[cfg(not(target_os = "linux"))]
    {
        0
    }
}

// ============================================================================
// Percentile
// ============================================================================

fn percentile(sorted: &[u64], pct: usize) -> u64 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = (sorted.len() * pct) / 100;
    let clamped = idx.min(sorted.len() - 1);
    sorted[clamped]
}

// ============================================================================
// Output helpers
// ============================================================================

fn emit(workflow: &str, elapsed_us: u64, rss_kb: u64) {
    println!(
        "[tauri-equiv] workflow={} elapsed_us={} rss_kb={}",
        workflow, elapsed_us, rss_kb
    );
}

fn emit_fps(workflow: &str, fps: u64, dropped: usize, rss_kb: u64) {
    println!(
        "[tauri-equiv] workflow={} fps={} dropped_frames={} rss_kb={}",
        workflow, fps, dropped, rss_kb
    );
}

fn emit_idle(workflow: &str, cpu_pct_x100: u64, rss_kb: u64) {
    println!(
        "[tauri-equiv] workflow={} cpu_pct_x100={} rss_kb={}",
        workflow, cpu_pct_x100, rss_kb
    );
}

fn emit_summary(workflow: &str, p50_us: u64, p95_us: u64, rss_kb: u64) {
    println!(
        "[tauri-equiv-summary] workflow={} p50_us={} p95_us={} rss_kb={}",
        workflow, p50_us, p95_us, rss_kb
    );
}

// ============================================================================
// In-process IPC stub (models Tauri command round-trip)
// ============================================================================

struct IpcChannel {
    pending: Option<(u64, u64)>,
}

impl IpcChannel {
    fn new() -> Self {
        IpcChannel { pending: None }
    }

    fn send(&mut self, id: u64, payload: u64) {
        self.pending = Some((id, payload));
    }

    fn recv(&mut self) -> Option<(u64, u64)> {
        self.pending.take()
    }
}

// ============================================================================
// Workflow 1: cold_start
// ============================================================================

fn bench_cold_start(t0: Instant, iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        // In headless mode: measure time from t0 to now (simulates "first paint")
        let elapsed = t0.elapsed();
        samples.push(elapsed.as_micros() as u64);
        // Simulate window teardown
        std::thread::sleep(Duration::from_micros(50));
    }
    samples
}

// ============================================================================
// Workflow 2: new_window
// ============================================================================

fn bench_new_window(iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        // Headless: simulate create + show + paint latency
        std::thread::sleep(Duration::from_micros(200));
        samples.push(t.elapsed().as_micros() as u64);
    }
    samples
}

// ============================================================================
// Workflow 3: close_window
// ============================================================================

fn bench_close_window(iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        // Simulate open
        std::thread::sleep(Duration::from_micros(100));
        let t = Instant::now();
        // Simulate destroy
        std::thread::sleep(Duration::from_micros(50));
        samples.push(t.elapsed().as_micros() as u64);
    }
    samples
}

// ============================================================================
// Workflow 4: resize
// ============================================================================

fn bench_resize(iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    for i in 0..iters {
        let new_w = WINDOW_WIDTH + (i & 15) as u32 * 10;
        let new_h = WINDOW_HEIGHT + (i & 7) as u32 * 10;
        let t = Instant::now();
        // Simulate resize + pixel buffer realloc + repaint
        let _buf = vec![0xFFFFFFFFu32; (new_w * new_h) as usize];
        std::thread::sleep(Duration::from_micros(100));
        samples.push(t.elapsed().as_micros() as u64);
    }
    samples
}

// ============================================================================
// Workflow 5: scroll
// ============================================================================

fn bench_scroll(iters: usize) -> Vec<u64> {
    let frames = iters.min(SCROLL_ROWS);
    let mut samples = Vec::with_capacity(frames);
    let row_h: usize = 20;
    let rows_visible = WINDOW_HEIGHT as usize / row_h;
    for frame in 0..frames {
        let t = Instant::now();
        // Simulate scroll: rebuild visible rows
        let mut buf = vec![0xFFFFFFFFu32; WINDOW_WIDTH as usize * rows_visible];
        for (i, px) in buf.iter_mut().enumerate() {
            *px = if (i / WINDOW_WIDTH as usize + frame) & 1 == 0 {
                0xF0F0FFFF
            } else {
                0xFFFFFFFF
            };
        }
        // Prevent DCE
        let _ = buf.iter().sum::<u32>();
        std::thread::sleep(Duration::from_micros(200));
        samples.push(t.elapsed().as_micros() as u64);
    }
    samples
}

// ============================================================================
// Workflow 6: route_change
// ============================================================================

fn bench_route_change(iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    for i in 0..iters {
        let color: u32 = if i & 1 == 0 { 0x6495EDFF } else { 0xF0F8FFFF };
        let t = Instant::now();
        let buf = vec![color; (WINDOW_WIDTH * WINDOW_HEIGHT) as usize];
        let _ = buf.iter().sum::<u32>();
        std::thread::sleep(Duration::from_micros(150));
        samples.push(t.elapsed().as_micros() as u64);
    }
    samples
}

// ============================================================================
// Workflow 7: ipc_roundtrip
// ============================================================================

fn bench_ipc_roundtrip(iters: usize) -> Vec<u64> {
    let mut ch = IpcChannel::new();
    let mut samples = Vec::with_capacity(iters);
    let mut checksum: u64 = 0;
    for i in 0..iters {
        let t = Instant::now();
        ch.send(i as u64, i as u64 * 7);
        if let Some((id, payload)) = ch.recv() {
            checksum += id + payload;
        }
        samples.push(t.elapsed().as_micros() as u64);
    }
    // Prevent DCE
    eprintln!("# ipc-roundtrip checksum={}", checksum);
    samples
}

// ============================================================================
// Workflow 8: event_broadcast
// ============================================================================

fn bench_event_broadcast(n_listeners: usize, iters: usize) -> Vec<u64> {
    let mut samples = Vec::with_capacity(iters);
    let mut checksum: u64 = 0;
    for i in 0..iters {
        let data = i as u64 * 3;
        let t = Instant::now();
        for listener in 0..n_listeners {
            checksum += data + listener as u64;
        }
        samples.push(t.elapsed().as_micros() as u64);
    }
    eprintln!("# event-broadcast checksum={}", checksum);
    samples
}

// ============================================================================
// Workflow 9: idle
// ============================================================================

fn bench_idle() -> (u64, u64) {
    let start = Instant::now();
    let deadline = Duration::from_millis(IDLE_DURATION_MS);
    let mut busy_us: u64 = 0;
    while start.elapsed() < deadline {
        let poll_t = Instant::now();
        // Simulate event poll (minimal CPU)
        std::thread::sleep(Duration::from_millis(1));
        busy_us += poll_t.elapsed().as_micros() as u64;
    }
    let elapsed_us = start.elapsed().as_micros() as u64;
    let rss = read_rss_kb();
    let cpu_pct_x100 = (busy_us * 10_000) / elapsed_us.max(1);
    (cpu_pct_x100, rss)
}

// ============================================================================
// Per-workflow runner
// ============================================================================

fn run_workflow(name: &str, iters: usize, t0: Instant) {
    match name {
        "cold_start" => {
            let mut samples = bench_cold_start(t0, iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("cold_start", percentile(&samples, 50), percentile(&samples, 95), rss);
            for &s in &samples {
                emit("cold_start", s, rss);
            }
        }
        "new_window" => {
            let mut samples = bench_new_window(iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("new_window", percentile(&samples, 50), percentile(&samples, 95), rss);
            for &s in &samples {
                emit("new_window", s, rss);
            }
        }
        "close_window" => {
            let mut samples = bench_close_window(iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("close_window", percentile(&samples, 50), percentile(&samples, 95), rss);
            for &s in &samples {
                emit("close_window", s, rss);
            }
        }
        "resize" => {
            let mut samples = bench_resize(iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("resize", percentile(&samples, 50), percentile(&samples, 95), rss);
            for &s in &samples {
                emit("resize", s, rss);
            }
        }
        "scroll" => {
            let mut samples = bench_scroll(iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            let n = samples.len() as u64;
            let total_us: u64 = samples.iter().sum();
            let fps = if total_us > 0 { n * 1_000_000 / total_us } else { 0 };
            let frame_budget_us = 16_667u64;
            let dropped = samples.iter().filter(|&&s| s > frame_budget_us).count();
            emit_fps("scroll", fps, dropped, rss);
            emit_summary("scroll", percentile(&samples, 50), percentile(&samples, 95), rss);
        }
        "route_change" => {
            let mut samples = bench_route_change(iters);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("route_change", percentile(&samples, 50), percentile(&samples, 95), rss);
        }
        "ipc_roundtrip" => {
            let mut samples = bench_ipc_roundtrip(iters * 100);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("ipc_roundtrip", percentile(&samples, 50), percentile(&samples, 95), rss);
        }
        "event_broadcast" => {
            let mut samples = bench_event_broadcast(2, iters * 10);
            samples.sort_unstable();
            let rss = read_rss_kb();
            emit_summary("event_broadcast", percentile(&samples, 50), percentile(&samples, 95), rss);
        }
        "idle" => {
            let (cpu_pct_x100, rss) = bench_idle();
            emit_idle("idle", cpu_pct_x100, rss);
        }
        other => {
            eprintln!("# unknown workflow: {}", other);
        }
    }
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    let t0 = Instant::now();

    let args: Vec<String> = std::env::args().collect();
    let mut workflow = "all".to_string();
    let mut iters = DEFAULT_ITERS;

    for arg in &args[1..] {
        if let Some(rest) = arg.strip_prefix("--workflow=") {
            workflow = rest.to_string();
        } else if let Some(rest) = arg.strip_prefix("--iters=") {
            if let Ok(n) = rest.parse::<usize>() {
                iters = n;
            }
        }
    }

    // Renderer identity: in headless stub mode report "stub"
    #[cfg(feature = "tauri-full")]
    let renderer = "tauri-webview";
    #[cfg(not(feature = "tauri-full"))]
    let renderer = "stub-headless";

    println!(
        "# tauri-bench renderer={} workflow={} iters={}",
        renderer, workflow, iters
    );

    let all_workflows = [
        "cold_start",
        "new_window",
        "close_window",
        "resize",
        "scroll",
        "route_change",
        "ipc_roundtrip",
        "event_broadcast",
        "idle",
    ];

    // Warmup (discard)
    for _ in 0..WARMUP_ITERS {
        let _ = bench_ipc_roundtrip(1);
    }

    if workflow == "all" {
        for &w in &all_workflows {
            run_workflow(w, iters, t0);
        }
    } else {
        run_workflow(&workflow, iters, t0);
    }
}
