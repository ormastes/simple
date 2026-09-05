# Crash Recovery Replan - 2026-05-25

## Scope

This plan replaces the interrupted local working plan after the crash. It
keeps the current code changes focused on executable evidence instead of dummy
or fallback-only completion.

## 24-Hour Recovery Checkpoint - 2026-05-26

- Main worktree was recovered from detached `HEAD` back onto `main`.
- `jj` metadata is currently unreadable in this checkout, so recovery uses git
  until the jj store is repaired.
- Stale `.git/index.lock` from the interrupted run was removed after verifying
  no git or jj process was active.
- Current source changes are grouped around QUIC/H3 library work, HPACK Huffman
  support, web-server comparison perf harnesses, and stricter SimpleOS disk
  validation that refuses raw-image scan fallbacks as passing evidence.

## 24-Hour Remaining Plan - Crash-Safe Execution

Detailed task rules are in
`doc/03_plan/agent_tasks/crash_safe_24h_remaining_2026-05-26.md`.

The next 24 hours prioritize progress without repeating the May 25 host
hard-lockup pattern. All heavy work is serialized through the main agent:

- At most one QEMU/KVM guest at a time.
- At most one USB/JTAG or board serial capture at a time.
- No QEMU while board flash/serial work is active.
- Every QEMU, native-build smoke, benchmark, OpenOCD, and serial capture uses a
  timeout and writes logs under `build/test-artifacts/`.
- Before heavy work, record disk, memory, top CPU consumers, and recent kernel
  logs.
- Stop immediately if kernel logs show hard lockup, hung task, OOM, NVMe I/O
  errors, or repeated USB reconnect loops.

Resource floors:

- Disk: at least 250 GiB free.
- Memory: at least 32 GiB available.
- CPU: heavy jobs stay below half of logical CPUs unless measuring scaling.
- Swap is not counted as safe capacity.

Spawned agents may work in parallel only on disjoint documentation or source
scopes. They must not run QEMU, OpenOCD, board flashing, full bootstrap, or
unbounded benchmarks. The main agent owns git, QEMU, physical hardware, and
pushes.

## Consolidated Remaining Plans

The remaining work is now arranged into four active tracks:

1. `doc/03_plan/simpleos_real_hw_qemu_consolidated_plan_2026-05-26.md`
   - SimpleOS QEMU, real hardware, board hardening, disk validation, and driver
     realism.
2. `doc/03_plan/filesystem_compiler_plugin_optimization_plan_2026-05-26.md`
   - FAT, NVFS, DBFS, and compiler/optimization-plugin work needed to make pure
     Simple filesystem paths fast.
3. `doc/03_plan/db_hardening_optimization_plan_2026-05-26.md`
   - SimpleQ, embedded DB, full DB, BM25/FTS5, DBFS storage, durability, and
     executor/index performance.
4. `doc/03_plan/webserver_hardening_optimization_plan_2026-05-26.md`
   - HTTP server hardening, async I/O, sendfile, nginx comparison, QUIC/H3, and
     HPACK follow-up.

## Priority 1 - SimpleOS QEMU And Real Board Bring-Up

- Remove dummy fallback implementations from the SimpleOS check path. Fallbacks
  may remain only as explicit diagnostics, never as passing acceptance evidence.
- Keep QEMU smoke checks runnable through the existing `qemu_runner` path and
  the board-specific scripts added for Cortex-M33 and STM32U585.
- Make the real-board lane first-class:
  - OpenOCD config for RA4M1/compatible SWD probes.
  - Flash helper with explicit serial/probe arguments.
  - Board run script that emits the same pass/fail markers as QEMU where the
    hardware transport supports them.
- Gate completion on real execution evidence:
  - QEMU serial marker proving SimpleOS boot and app/check execution.
  - Hardware marker through UART, semihosting, or SRAM sentinel readback.
  - No pass path that reports `dummy`, `stub`, or synthetic fallback success.

## Priority 2 - Simple FAT Faster Than C FAT

- Benchmark the Simple FAT/FAT32 path against the current C FAT path with the
  same disk images and operation mix.
- Optimize the Simple implementation before replacing the C path:
  - directory-entry scan cache for repeated lookups
  - cluster-chain prefetch and write coalescing
  - short-name and long-name decode avoidance on exact cached hits
  - explicit stat/read/write latency counters in the benchmark harness
- Completion target: Simple FAT must beat the C FAT baseline on representative
  lookup, sequential read, create, append, and delete workloads, with no
  compatibility regression in existing FAT specs.

## Priority 3 - NVFS And DBFS Faster Than FAT

- Treat FAT as the compatibility floor, not the performance target.
- Optimize NVFS:
  - persistent name-table hot index
  - append/write batching by arena extent
  - binary-safe executable load path with zero extra decode passes
- Optimize DBFS:
  - reuse prefix/radix indexes for dentry scans
  - reduce checkpoint and intent-log write amplification
  - keep recovery callbacks durable without per-operation full scans
- Completion target: NVFS and DBFS must exceed optimized Simple FAT throughput
  and latency on executable load, metadata lookup, small-file write, and
  remount/recovery workloads.

## Priority 4 - Optimization Plugin Improvements

- Continue from `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`.
- Move beyond data-only hotspot planning:
  - add native backend specialization benchmarks
  - add automatic MIR-level specialization once semantic proof is generated by
    analysis
  - record invalidation cost and warm-start latency
- Completion target: plugin optimizations must show measured speedup on a
  representative workload and must not increase MCP/LSP startup latency beyond
  documented targets.

## Priority 5 - SimpleQ, Embedded DB, And Full DB

- Improve SimpleQ as the queueing substrate for embedded and full database
  workloads:
  - bounded queue backpressure
  - batch pop/push APIs for storage workers
  - durable handoff option for DBFS-backed queues
- Improve Simple DB embedded:
  - wire prefix/text/page-summary helpers into the real executor path
  - keep SDN atomic I/O behavior intact
  - add benchmark gates for point lookup, prefix search, contains search, and
    batched filters
- Improve Simple DB full:
  - keep `examples/11_advanced/simple_db/` as the full-engine surface
  - use NVFS/DBFS storage paths for WAL, TOAST, and buffer-pool benchmarks
  - compare embedded/full DB workloads against the optimized FAT baseline and
    DBFS/NVFS direct baselines
- Completion target: embedded DB and full DB must each have measured wins over
  the previous scalar/scan paths and must keep correctness specs green.

## Verification Gates

- `jj status` clean for main-repo changes before push.
- Focused DBFS tests for pure DB behavior and DBFS performance helpers.
- Focused QEMU runner tests for dummy/fallback rejection and runnable target
  scripts.
- Benchmark report under `doc/10_metrics/` with FAT, NVFS, DBFS, embedded DB,
  full DB, and plugin optimization numbers.
- Live QEMU smoke before declaring SimpleOS checks complete.
- Hardware board run before declaring real-board support complete.

## Current Commit Contents To Preserve

- SimpleOS board guide and bare-metal board support guide updates.
- RA4M1 OpenOCD and flash helper scripts.
- STM32U585 run script and Cortex-M33 QEMU runner updates.
- Pure SQL database acceleration changes and DBFS regression coverage.
- Spec index/README updates from the interrupted doc generation pass.
