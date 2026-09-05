# Research: SimpleOS Perf + Benchmark Harness + API/Arch Guard

Domain: SimpleOS x86_64 perf · cross-cutting benchmark harness · sspec arch-tagging · API/arch guard
Date: 2026-06-13

---

## SimpleOS Perf — DONE vs OPEN

Related spipe goals investigated (all phase-checked via state.md):

| Spipe Goal | Phase Status | Key Outcomes |
|---|---|---|
| `harden-nvfs-simpleos` | **CLOSED** 2026-04-24 (`0515a3d0b7`) | NVFS hardening + POSIX compat, FAT32 read + allocator, drivers |
| `fs-hardening-optimization` | **CLOSED** 2026-05-23 | FS profiling harness, 9/15+11/11+12/14 waves; 6 pre-existing blockers deferred |
| `fs-opt-general` | **CLOSED** 2026-05-23 | MIR optimizer improvements (struct-array-loop), C extern → pure Simple (rt_bytes_alloc, rt_text_to_bytes), FAT32 vs VFAT comparison at `doc/10_metrics/fs_driver_vfat_comparison.md` |
| `scheduler-process-isolation` | **CLOSED** 2026-05-20 | Process isolation + scheduler; duplication analysis at `doc/05_design/scheduler_process_isolation_duplication_analysis.md`; no public symbol duplication found |
| `qemu-perf-session` | **OPEN** (phase 1-dev in progress) | QemuBroker session pooling; perf bug triage: `pure_simple_ctype_perf_gap` still open (Cranelift AOT no inlining); `interpreter_1460x_c_perf_gap` not a bug (expected gap); collection parity RESOLVED 2026-05-15 |

**Net OPEN for this goal:** `pure_simple_ctype_perf_gap` (Cranelift inlining), QEMU broker session sharing, x86_64 baseline benchmark numbers not yet captured.

---

## QEMU Systest Model (for AC-3 arch-extensible benchmarks)

The existing QEMU system test infrastructure is the correct model for arch-tagged reusable specs.

**File layout pattern** (`test/03_system/os/qemu/os/`):
- `common/qemu_os_config.spl` — centralizes per-arch `OsTarget` descriptors (reuses `os.qemu_runner.{OsTarget, get_target, arch_from_name, build_qemu_command}`)
- `common/qemu_os_harness.spl` — shared boot + serial harness
- `boot/x86_64_boot_qemu_spec.spl`, `arm64_boot_qemu_spec.spl`, `riscv64_boot_qemu_spec.spl`, etc. — one per-arch spec file
- `appscan/x86_smf_appscan_qemu_spec.spl`, `arm_smf_appscan_qemu_spec.spl` — cross-arch scan tests

**Per-arch descriptor contract** (`src/os/qemu_systest_contract.spl`):
- Hardcodes QEMU argv per arch (x86_64, arm32, arm64, riscv32, riscv64, x86_32) from lane reference data; does NOT call `simpleos_platform_*` (crashes in interpreter mode)
- Provides classifiers: `SYSTEST_PASS`, `SYSTEST_PREFIX_MISSING_MEDIA`, `SYSTEST_PREFIX_BOOT_FAIL`, `SYSTEST_BOOT_FAIL_FALLBACK`
- Exit code: x86/x86_64 with isa-debug-exit → exit code 1 = success; arm64/riscv semihosting → 0 = success
- Serial logs → `build/os/systest/<arch>.serial.log`

**2026-06-13 multiarch plan** (`doc/03_plan/os/simpleos/qemu_system_tests_multiarch_2026-06-13.md`):
- Track B: `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl` for 6 arches (riscv64, riscv32, arm32, arm64, x86_64, x86_32) — boot real QEMU, assert markers + `fs_exec_serial_has_fallback == false`
- This is directly reusable as the benchmark harness model for AC-3

---

## sspec Arch-Tagging — What Exists, What's Needed

**What exists:**
- `src/lib/nogc_sync_mut/spec/decorators.spl` and `src/lib/nogc_sync_mut/spec/mod.spl` provide a `skip()` decorator with named fields: `platforms`, `runtimes`, `profiles`, `architectures`, `features`, `hardware`, `tags`, `dependencies`, `env_vars`, `fs_features`, `network`, `reason`
- Usage: `skip(architectures: ["arm64"], reason: "...")` applied to a `describe`/`it` block — returns a decorated wrapper used as `skip_arm "test name": ...`
- The `architectures` field already exists for conditional skip; `tags` field is also present

**What's MISSING for reusable arch-tagged benchmarks (AC-3):**
1. No `only_on(architectures: [...])` positive-select (only skip variants exist); need a positive filter or convention
2. No tag-based CLI filter for `bin/simple test --tag=x86_64` to select a subset of specs at test-run time — the `tags` field on `skip()` is recorded but no runner-side `--filter-tag` flag is confirmed present
3. No arch-parameterized describe block (one describe that loops arches) — current pattern is one spec file per arch; for benchmarks, a single spec file parameterized over arches via a config struct is cleaner

**Recommended approach (no API change needed for P0):**
- Benchmark specs use the existing `skip(architectures: [...])` to gate non-applicable arches; x86_64 runs now, others skip
- A shared config struct (like `OsTarget` in `qemu_os_config.spl`) drives arch-specific parameters
- Track gap: file a feature request for `--filter-tag` CLI and `only_on()` positive decorator for AC-3 full extensibility

---

## Cross-Language Perf Harness Details (AC-3, AC-10)

**Script:** `scripts/check/check-cross-language-perf.shs`

**Dimensions measured:**
- Binary/runtime size
- Cold startup latency
- Warm throughput: fib(N=35) in-process loop (default RUNS=20) — JIT runtimes reach steady state in a single process
- Parallel CPU workers (default 100)
- Large fanout scheduling (FANOUT_WORKERS, FANOUT_ITERS, FANOUT_STRESS_WORKERS)

**Languages compared:** Simple interpreter / SMF loader / native Cranelift, Bun, Python, Go, Erlang, Java, C

**Output:**
- `REPORT_PATH` defaults to `doc/09_report/cross_language_perf_<date>.md` — Markdown report
- Optional Docker isolation (`PROFILE_DOCKER_ISOLATION=1`) for reproducibility
- Contract test: `test/05_perf/profile_scripts/profile_report_contract_test.shs` validates report shape

**For AC-3 benchmark docs:** The harness already emits to `doc/09_report/`; sspec benchmark specs should do likewise or call this script and embed results.

---

## API/Arch GUARD Options (AC-8)

**Existing tooling:**
- `src/compiler/99.loader/metadata_symbol_surface.spl` and `metadata_symbols.spl` — metadata-level symbol index per module (path, count, named symbols s0..s3); queryable via `symbols_for(path)` and `has_path(path)` — basis for a public surface snapshot
- `src/compiler/90.tools/symbol_analyzer.spl` + `symbol_root_registry.spl` — symbol-level analysis tooling already present
- `src/compiler/70.backend/linker/symbol_analysis.spl` + `elf_symbols.spl` — ELF symbol inspection for native builds
- `src/compiler/00.common/dependency/symbol.spl` — dependency symbol model
- `scheduler-process-isolation` refactor already proved no public symbol duplication via a design doc (`doc/05_design/scheduler_process_isolation_duplication_analysis.md`)

**No snapshot-and-diff guard exists today.** There is no automated "capture public API surface → diff before/after optimization" step.

**Recommended guard approach (AC-8):**
1. **Snapshot step (P0):** Use `symbol_analyzer.spl` + `metadata_symbol_surface.spl` to emit a `doc/08_tracking/api_surface_snapshot_<date>.sdn` capturing exported symbols per module before any optimization
2. **Diff step (post-opt):** Re-run and diff the SDN; any removed/renamed export is a hard block
3. **Accessor-forwarding spec:** sspec test asserting that accessor wrappers (cache-invalidation paths) still call through to the same underlying fns — checked in interpreter mode
4. **Arch-doc parity:** `doc/04_architecture/` docs for each optimized domain must be re-verified unchanged after the optimization; a checklist in the plan doc suffices for P0

**Architecture doc locations:** `doc/04_architecture/os/simpleos/`, `doc/04_architecture/compiler/`, `doc/04_architecture/adr/`

---

## Benchmark Doc Location

| Doc type | Where |
|---|---|
| Temporal benchmark reports (per-run dated) | `doc/09_report/` (existing convention: `cross_language_perf_<date>.md`, `startup_size_performance_audit_<date>.md`) |
| Persistent metrics / comparison tables | `doc/10_metrics/` (existing: `fat32_vs_cfat_benchmark.md`, `fs_driver_vfat_comparison.md`) |
| Generated spec docs | `doc/06_spec/test/...` (mirrors test/ path; DO NOT refactor) |
| Baseline snapshot SDN | `doc/08_tracking/` (auto-gen; alongside test_db) |

**Recommendation:** Benchmark docs emitted by sspec → `doc/09_report/perf_benchmark_<domain>_<arch>_<date>.md`; persistent comparison tables → `doc/10_metrics/perf/`; API surface snapshots → `doc/08_tracking/api_surface/`.

---

## Risks

1. **sspec tag/filter gap** — No confirmed `--filter-tag` CLI in `bin/simple test`; arch-gating via `skip(architectures:)` works but requires one spec per arch or manual filtering. File feature request before P0 spec phase.
2. **qemu-perf-session still open** — Session broker not yet wired; benchmark boot overhead per test is high without it. Unblock before OS benchmark runs.
3. **pure_simple_ctype_perf_gap** — Cranelift AOT inlining missing; x86_64 native perf ceiling limited. Must document as known gap in P0 baseline.
4. **No public API snapshot tooling (automated)** — Existing symbol tools need a thin harness wrapper to produce diffable snapshots; build this in P0 before any optimization lands.
5. **Interpreter false-greens** — `--mode=native` stub no-ops, `--mode=smf` swallows errors; all benchmark specs must verify in interpreter mode first.
6. **fs-hardening 6 pre-existing blockers** — Deferred from CLOSED goal; may re-surface as open perf gaps in OS domain. Audit at P2 entry.
