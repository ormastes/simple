# Simple GUI vs Rust+Tauri Benchmark

Equivalent app workflow benchmarks for Simple GUI vs Rust+Tauri (NFR 2B / Workstream 9).

## Files

| File | Role |
|------|------|
| `simple_app.spl` | Simple GUI benchmark app (SDL2 backend) |
| `tauri_reference/src/main.rs` | Rust+Tauri reference (headless stub by default) |
| `tauri_reference/Cargo.toml` | Tauri dependency manifest |
| `workflow_driver.spl` | Orchestrates both apps, prints comparison table |
| `report_spec.spl` | Unit tests for parser, ratio, NFR gates |

## Quick Start

Run the spec (unit tests only, no display needed):

```sh
bin/simple test test/perf/tauri_equiv/report_spec.spl
```

Run the Simple benchmark app alone:

```sh
bin/simple run test/perf/tauri_equiv/simple_app.spl --iters=20
```

Build and run the Tauri reference (headless stub, no display needed):

```sh
cargo build --release --manifest-path test/perf/tauri_equiv/tauri_reference/Cargo.toml
test/perf/tauri_equiv/tauri_reference/target/release/tauri-bench --iters=20
```

Run the full comparison driver:

```sh
bin/simple run test/perf/tauri_equiv/workflow_driver.spl --iters=20
```

## Workflows Measured

| # | Workflow | NFR 2B Gate |
|---|----------|-------------|
| 1 | `cold_start` | Simple ≤ 1.00x Tauri (equal-or-better, or idle RSS ≤ 1.00x) |
| 2 | `new_window` | Simple ≤ 1.25x Tauri p95 |
| 3 | `close_window` | Measured; informational |
| 4 | `resize` | Simple ≤ 1.25x Tauri p95 |
| 5 | `scroll` | Simple ≤ 1.25x Tauri p95 |
| 6 | `route_change` | Measured; informational |
| 7 | `ipc_roundtrip` | Simple ≤ 1.25x Tauri p95 |
| 8 | `event_broadcast` | Measured; informational |
| 9 | `idle` | Simple RSS ≤ Tauri RSS (equal-or-better gate) |

## Output Format

Each app emits to stdout:

```
[tauri-equiv] workflow=<name> elapsed_us=<N> rss_kb=<N>
[tauri-equiv-summary] workflow=<name> p50_us=<N> p95_us=<N> rss_kb=<N>
[tauri-equiv] workflow=idle cpu_pct_x100=<N> rss_kb=<N>
```

The `workflow_driver.spl` parses both outputs and prints the comparison table with `simple_vs_tauri_ratio` for each workflow.

## NFR 2B Requirements (Option 2B)

- Simple GUI must be **equal-or-better** than Tauri on at least one of: `cold_start` p95 OR `idle` RSS.
- Simple GUI must be **within 1.25x** of Tauri on: `new_window`, `scroll`, `resize`, `ipc_roundtrip` p95.
- `workflow_driver.spl` exits non-zero if either gate fails.

## Notes

- `tauri_reference` compiles as a headless stub by default (no real Tauri/WebView dependency).
  Use `--features tauri-full` for a real Tauri window build (requires display + Tauri 1.x).
- `simple_app.spl` gracefully degrades to stub output if SDL2 is unavailable (CI mode).
- All timing uses `rt_time_now_nanos()` / `rt_sdl2_*` for monotonic wall-clock accuracy.
- Report columns: `workflow`, `simple_p50_us`, `simple_p95_us`, `tauri_p50_us`, `tauri_p95_us`,
  `simple_rss_kb`, `tauri_rss_kb`, `simple_vs_tauri_ratio`.
