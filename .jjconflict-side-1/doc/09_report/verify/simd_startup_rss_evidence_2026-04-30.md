# SIMD Startup And RSS Evidence

Date: 2026-04-30
Scope: approved remaining SIMD tranche, startup-regression evidence only

STATUS: PASS

Measurement facilities used:
- driver startup phase reporting via `--startup-metrics`
- external wall-clock and max RSS via `/usr/bin/time`
- existing startup perf validation spec: `test/integration/app/startup_argparse_mmap_perf_spec.spl`
- existing driver startup tests: `src/compiler_rust/driver/tests/startup_optimization_test.rs`

Binary and runtime path:
- binary: `src/compiler_rust/target/release/simple`
- exercised path: `simple --startup-metrics run <tiny script>`
- probe script body:

```simple
fn main():
    print "startup-simd-probe"
```

Host details:
- OS: `Linux 6.8.0-107-generic`
- arch: `x86_64`
- CPU: `AMD Ryzen Threadripper 1950X 16-Core Processor`
- local SIMD capability observed: `avx2`
- limitation: this host cannot provide NEON startup evidence, so the checked-in evidence is for the current x86_64 runtime path only

Exact commands:

```bash
tmpdir=$(mktemp -d)
cat > "$tmpdir/startup_simd_probe.spl" <<'EOF'
fn main():
    print "startup-simd-probe"
EOF

for i in 1 2 3; do
  /usr/bin/time -f "sample=$i real=%e rss_kb=%M" \
    src/compiler_rust/target/release/simple \
    --startup-metrics run "$tmpdir/startup_simd_probe.spl" \
    >/tmp/startup-simd-probe-$i.out \
    2>/tmp/startup-simd-probe-$i.err
done

rm -rf "$tmpdir"
```

Warm startup samples:
- `sample=1 real=0.01 rss_kb=19712`
- `sample=2 real=0.01 rss_kb=19968`
- `sample=3 real=0.01 rss_kb=19968`

Internal startup-metrics totals from the same runs:
- sample 1 total: `7.283152ms`
- sample 2 total: `7.206305ms`
- sample 3 total: `4.793796ms`

Representative phase breakdown seen on the measured path:
- Early Argument Parsing: `0.05ms` to `0.08ms`
- File Prefetching: `0.24ms` to `0.35ms`
- Logging Init: `3.23ms` to `5.04ms`
- Database Cleanup: `0.26ms` to `0.46ms`
- Signal Handler Init: `0.08ms` to `0.12ms`

Summary:
- warm startup for the current runtime path is consistently `0.01s` externally
- max RSS across sampled runs is `19968 KB`
- internal startup phase totals remain below `8ms` on all measured warm runs
- no local startup regression evidence was observed from the current SIMD runtime additions on this host

Required evidence markers:
- warm startup: present
- max rss: present
- host limitation for NEON comparison: documented
