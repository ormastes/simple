# nginx Baseline Benchmark — 2026-05-27

## Environment

- **Machine:** Linux 6.8.0-117-generic, x86_64
- **nginx:** 1.24.0 (Ubuntu), worker_processes auto, sendfile on
- **Tool:** wrk -t4 -c50 -d10s (4 threads, 50 concurrent connections, 10s)
- **Fixtures:** Local loopback (127.0.0.1:8080), static HTML files

## Results

| File | Size | RPS | Avg Latency | Max Latency | Throughput |
|------|------|-----|-------------|-------------|------------|
| small.html | 1 KB | 199,517 | 208 us | 6.50 ms | 242 MB/s |
| medium.html | 64 KB | 75,589 | 4.42 ms | 43.69 ms | 4.63 GB/s |
| large.html | 1 MB | 8,957 | 3.19 ms | 17.16 ms | 8.75 GB/s |

## Notes

- nginx uses sendfile(2) for zero-copy static file serving
- Large file throughput is bandwidth-limited (loopback), not CPU-limited
- Small file RPS is ~200K — this is the target for Simple's compiled mode
- Simple server cannot run in interpreter mode (unresolved `rt_text_to_i64` extern)
- Simple benchmark pending compiled-mode server availability

## Target for Simple

To be competitive, Simple's compiled HTTP server should aim for:
- Small files: >50K RPS (25% of nginx) as initial milestone
- Medium files: >20K RPS (sendfile routing critical)
- Large files: bandwidth-bound — should match nginx once sendfile is wired
