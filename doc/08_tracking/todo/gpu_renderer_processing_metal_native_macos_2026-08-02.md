# TODO 652 — Admit Metal MSL ProcessingIR and Drawing Readback on macOS

- Status: open / native row blocked on pure-Simple binary availability, NOT on
  the host (2026-09-17 sweep on the physical M4: host + Metal toolchain are
  fully capable; no admitted source-matched pure-Simple macOS binary can reach
  the device probe — see the 2026-09-17 update below).

## 2026-09-17 update (macOS sweep)

Host: MacBook Air, Apple M4, Darwin 25.5.0 arm64. All evidence under
`build/gpu_renderer_processing_backends/metal_msl/` (logs/, artifacts/, probe/).

### Host capability (TODO's own prerequisite probes — PASS)

```
$ xcrun --find metal    # /var/run/.../Metal.xctoolchain/usr/bin/metal
$ xcrun --find metallib # /var/run/.../Metal.xctoolchain/usr/bin/metallib
$ system_profiler SPDisplaysDataType -> Chipset Model: Apple M4; Metal Support: Metal 4
$ probe/host_metal_probe (clang -framework Metal, logs/host-metal-probe-2026-09-17.log):
  HOST_METAL_PROBE available=1 name=Apple M4 registry_id=4294968465 metal3=1
  recommended_max_working_set_bytes=19069665280 low_power=0 headless=0 removable=0
```

### Generated MSL compiles with the real Apple toolchain (PASS)

`processing_metal_source` output for FillU32 and FillRect (emitted via seed
`bin/simple run probe/emit_msl.spl`) compiled clean:
`xcrun metal -c *.metal -> *.air`, `xcrun metallib *.air -> processing.metallib`.
Retained at `artifacts/processing_fill.metal`, `processing_fill_rect.metal`,
`*.air`, `processing.metallib` (`logs/xcrun-metal-compile-2026-09-17.log`).

### Binary matrix — which binary ran, and what happened

| Binary | Metal linkage | Result |
|--------|---------------|--------|
| `bin/simple` (Rust seed, rebuilt 2026-09-14) | none; `rt_metal_init == rt_metal_is_available` @ 0x1007bab9c (same-address stubs) | runner works; spec runs and fails closed (below) |
| `bin/release/aarch64-apple-darwin-macho/simple` (pure-Simple, built 2026-09-07 16:38 KST from c438fee2139, 26,264,696 B) | links Metal.framework; `rt_metal_init` @ 0x100de3954, `rt_metal_is_available` @ 0x100f5a990 (distinct, real impl linked) | `test` SIGSEGVs in runner setup; `run` unusable (below) |
| `bin/release/aarch64-apple-darwin/simple` (2026-07-25) | links Metal.framework (adjacent symbols) | runner works, but its compiler cannot parse the current lib (`parse: process_ops.spl ... found Colon`) |

Macho binary failure detail (all reproduced 2026-09-17, logs probe-*.log):
- `simple test <spec> [--mode=interpreter] [--no-session-daemon]`
  → `Segmentation fault: 11` right after `[setup] cover-check`. Crash report
  `~/Library/Logs/DiagnosticReports/simple-2026-09-12-093053.000.ips` (same
  binary, same signature): EXC_BAD_ACCESS at 0x0, faulting frame
  `src__lib__nogc_sync_mut__daemon_sdk__client__daemon_ensure_running` (null
  start_fn call). `SIMPLE_REQUIRE_GPU=1` direct-lane bypass does not help — the
  crash precedes the bypass print.
- `SIMPLE_NO_BOOTSTRAP_DELEGATE=1 simple run <file.spl>` (in-process interpret):
  every run prints `[simple-runtime][error] rejected invalid array handle before
  dereference; probable compiler/FFI ABI mismatch`, then unresolved-name errors
  for every `use std.*` import; a plain `print("HELLO")` file SIGSEGVs.
- default `simple run <file.spl>` delegates to `bin/simple` (the seed) via
  `_cli_driver_binary()` → executes under the seed runtime (stub Metal) →
  probe answers `is_available=false device_count=0` (misleading: that is the
  seed, not the macho runtime).
- seed-compiled `.smf` executed by the macho binary → `Invalid SMF magic`
  (format drift between the two builds).
- Rebuilt macho binary + its own Sep-7 source snapshot (`git archive c438fee2139`,
  `SIMPLE_LIB=snapshot-2026-09-07/src`): identical failures → the defects are in
  the Sep-7 build itself, not staleness.

### Exact blocker

The native rows cannot be exercised end-to-end today: the only pure-Simple
macOS binary with a real Metal implementation (2026-09-07) cannot run the test
runner (setup SIGSEGV) or in-process interpretation (ABI mismatch + SIGSEGV),
and every fallback path silently executes under the Rust seed, whose
`rt_metal_*` symbols are same-address stubs that fail closed with
`metal-unavailable`. Unblocking requires the root lane to rebuild and admit a
current source-matched pure-Simple macOS binary (bootstrap re-deploy); the host,
the Metal toolchain, and the generated MSL are all verified good.

### System spec verdict (working binary = seed; todo's exact resume command)

```
$ SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl --mode=interpreter
✓ should generate a deterministic host-independent ProcessingIR artifact
✗ should require native device-origin readback and exact CPU oracle parity
    expected metal-unavailable to equal ok
✗ should preserve Metal-to-Metal fill rectangle coordinates and pixels
    expected false to equal true
SPEC FILE VERDICT ... outcome=ERROR declared>=3 executed=3 passed=1 failed=2
```
(logs/system-spec-seed-2026-09-17.log). This is the designed fail-closed shape
on a stub runtime: `is_macos()` is true under the seed, so the spec takes the
native branch and the stub runtime refuses with `metal-unavailable`.

### Perf spec authored and run (host-independent row)

`test/05_perf/processing/metal_msl_generation_perf_spec.spl` did not exist in
git history; authored per the doc gate wording and `test/05_perf` sibling
conventions (`web_render_chrome/*_spec.spl`: describe/it, `time_now_micros`,
warm real work, printed `KEY=value` summary, no placeholder assertions).
Budgets from `doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md`:
512 generations, average < 10 ms, procfs VmHWM incremental peak RSS < 8 MiB,
semantic-key invalidation for changed values/counts. The RSS assertion arms only
where procfs exists (`file_exists("/proc/self/status")` →
`process_peak_rss_kb`); on macOS it records `rss_measurable=false`.

```
$ SIMPLE_LIB=src bin/simple test test/05_perf/processing/metal_msl_generation_perf_spec.spl --mode=interpreter
✓ generates 512 deterministic artifacts under the latency and memory budgets
  PROCESSING_METAL_MSL_GEN_PERF generations=512 total_us=42984 average_us=83
  procfs_available=false rss_measurable=false rss_delta_kib=-1
  all_valid=true fill_u32_deterministic=true fill_rect_deterministic=true
✓ invalidates the semantic key when ProcessingIR value or count changes
  PROCESSING_METAL_MSL_KEY_INVALIDATION base_key=processing-ir-v2|metal-msl|op=1|...
SPEC FILE VERDICT ... outcome=OK declared>=2 executed=2 passed=2 failed=0
```
(logs/perf-spec-seed-diagnostic-2026-09-17.log; seed run is diagnostic-only per
the doc: average 83 µs vs the 10 000 µs budget). The same command must be
re-run with an admitted pure-Simple binary for admission; the RSS row will
assert on the procfs host used for admission.

Remaining open items: (1) root lane rebuilds + admits a source-matched
pure-Simple macOS binary; (2) re-run the system spec native rows on it — host
evidence here says they should pass; (3) re-run the perf spec on it for
admission numbers.
- Target host/hardware: physical Apple Silicon or Intel Mac running macOS with
  a Metal compute-capable GPU. Virtual, CPU-mirror, emulator, and Linux evidence
  cannot satisfy this row.
- Libraries/runtime: Apple `Metal.framework`, `Foundation.framework`, and
  `CoreGraphics.framework`, reached through the repository-owned `objc2-metal`
  runtime provider and the Simple Metal SFFI facade.
- Toolchain: Xcode Command Line Tools exposing `xcrun metal` and
  `xcrun metallib`; admitted source-matched pure-Simple `bin/simple`;
  `SIMPLE_LIB=src`; writable evidence root.
- Exact prerequisite probes: `xcrun --find metal` and
  `xcrun --find metallib`.
- Exact native resume command:
  `SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl --mode=interpreter`
- Exact host-independent performance command:
  `SIMPLE_LIB=src bin/simple test test/05_perf/processing/metal_msl_generation_perf_spec.spl --mode=interpreter`.
- Retained paths:
  - generated `.metal`, `.air`, `.metallib`, hashes, semantic keys, raw
    readback, CPU oracle, mismatch counts, latency, and RSS under
    `build/gpu_renderer_processing_backends/metal_msl/artifacts/`;
  - structured native lifecycle events at
    `build/gpu_renderer_processing_backends/metal_msl/events/native-events.ndjson`;
  - FillRect raw image evidence at
    `build/gpu_renderer_processing_backends/metal_msl/images/fill-rect-readback.rgba`;
  - compiler and system stdout/stderr at
    `build/gpu_renderer_processing_backends/metal_msl/logs/system.log`.
- Required result: FillU32 and Metal-to-Metal drawing source compile; native
  submission succeeds; raw device-origin readback exactly equals the CPU oracle;
  invalid/unsupported translation remains fail-closed.
- Linux unavailable-host result: the host-independent generator row passes,
  both native rows validate this metadata and then call `fail_test`; exit zero
  is forbidden while physical Metal evidence is unavailable.
- Owner: prepared-macOS evidence operator.
- Merge owner and final reviewer: root Codex agent (normal/highest-capability).
