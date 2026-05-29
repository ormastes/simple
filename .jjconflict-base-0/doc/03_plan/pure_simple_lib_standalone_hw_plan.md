# Pure Simple Library And Standalone Hardware Plan

## Goal

Move default library functionality from C/runtime-hosted implementations into
pure Simple under `src/lib`, while preserving explicit access to existing host C
libraries through SFFI provider ports. The final default target is hardware
friendly and fully standalone: no libc, no host shell, no hidden fallback pass
paths, and no dependency on C unless a selected provider explicitly requests it.

This plan extends:

- `doc/03_plan/port_rust_c_to_pure_simple.md`
- `doc/03_plan/agent_tasks/rust_runtime_minimization.md`
- `doc/03_plan/agent_tasks/custom_primitive_sffi_public_api.md`
- `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`
- `doc/05_design/platform_sffi_optional_features.md`
- `doc/05_design/hardware_driver_safety_and_performance_2026-04-15.md`

## Principles

- Pure Simple is the default implementation in `src/lib`.
- C libraries are provider backends, not semantic owners.
- SFFI access is explicit, typed, measured, and optional.
- Hardware access goes through typed Simple HAL ports first; raw MMIO or probe
  access is isolated to target capsules.
- If pure Simple is slow, fix compiler/runtime/optimization-plugin causes before
  delegating to C.
- Any C/SFFI fallback must be visible in logs, benchmarks, and build metadata.

## Phase 0 - Inventory And Baseline

1. Build a `src/lib` dependency inventory that classifies each module:
   - pure Simple already
   - Simple wrapper over C runtime helper
   - SFFI wrapper over host library
   - shell-out or process-backed host behavior
   - hardware-specific runtime hook
2. Record host C baseline implementations and commands for every replacement
   target, including libc, sqlite, compression, crypto, math/BLAS, filesystem,
   socket, terminal, time, and hardware probe paths.
3. Add a benchmark ledger under `doc/10_metrics/` comparing:
   - portable C baseline
   - host SFFI provider
   - pure Simple interpreter
   - pure Simple native
   - pure Simple LLVM native where available
4. Fail the inventory if a pass path silently uses shell, C, Rust, or host
   runtime fallback without naming the provider.

Exit evidence:

- One inventory report with module classification and owner.
- One baseline metric file with C/SFFI/Simple ratios.
- No unknown provider in the selected smoke lane.

## Phase 1 - Provider Shape: Pure First, SFFI Explicit

1. Define a repeated provider layout for migrated libraries:
   - `src/lib/<family>/<feature>.spl`: public pure Simple API
   - `src/lib/<family>/<feature>_pure.spl`: default implementation
   - `src/lib/<family>/<feature>_sffi.spl`: optional host C provider
   - `src/lib/<family>/<feature>_port.spl`: typed provider contract
   - `test/perf/<family>/<feature>_provider_bench.spl`: parity and speed
2. SFFI provider contracts must include:
   - availability probe
   - ABI/layout version
   - provider name and version string
   - feature flags
   - error mapping
   - deterministic fallback refusal when unavailable
3. Public APIs should accept domain types or transparent custom primitives for
   handles, sizes, offsets, addresses, file modes, IRQs, DMA addresses, errno,
   deadlines, and page IDs.
4. Raw primitives remain allowed only at exact SFFI/MMIO/ABI boundaries.

Exit evidence:

- Provider skeleton for one pilot library.
- SFFI custom primitive ABI tests for at least one handle, address, size, and
  error wrapper.
- Provider choice appears in benchmark output.

## Phase 2 - Port C Library Surfaces Into Pure Simple

Prioritize modules that unlock standalone builds:

1. Memory and byte primitives:
   - `memcpy`, `memmove`, `memset`, compare, scan, endian load/store
   - fixed-size stack buffers and typed `[u8]` lowering
2. String and text:
   - byte-safe UTF-8 scan, split, find, parse integer/float
   - no locale or libc dependence in standalone mode
3. Filesystem and storage:
   - Simple FAT/FAT32, NVFS, DBFS, path normalization, directory iteration
   - C FAT remains a benchmark/provider only until Simple FAT wins
4. Compression and checksums:
   - CRC32, Adler-32, XXHash, LZ4, Deflate, Zstd primitives
   - C/Rust baselines are correctness and speed references only
5. Crypto and TLS-support primitives:
   - constant-time compare, hash blocks, AEAD block loops, big-int limb loops
   - no table or branch change that violates constant-time requirements
6. SQLite and database:
   - embedded Simple DB first, full Simple DB through `examples/simple_db`
   - SQLite SFFI remains a host compatibility provider
7. Terminal, sockets, time, process:
   - Simple policy and protocol logic
   - minimal C/SFFI shims only for unavoidable OS syscalls on hosted targets

Exit evidence:

- Every migrated feature has parity tests against C/SFFI where applicable.
- Every feature has a native benchmark row.
- Standalone target excludes libc symbols unless explicitly selected.

## Phase 3 - Optimization Plugin Update

The optimization plugin must prevent the exact problem this plan creates: pure
Simple replacing a C library and becoming too slow.

Required plugin/provider work:

1. Add `CLibParityHotspot` facts for code that replaces known C library shapes:
   - byte copy/fill/compare
   - endian load/store
   - table lookup
   - checksum reducer
   - rotate/xor/add rounds
   - bit-reader loops
   - prefix/directory scans
   - MMIO polling loops
2. Add benchmark-informed provider metadata:
   - C baseline function name
   - pure Simple function name
   - current ratio
   - target ratio
   - last measured commit
   - permitted transforms
3. Add MIR transforms before backend codegen:
   - bounds-check elimination from explicit range facts
   - typed byte load/store canonicalization
   - fixed-size buffer stack lowering
   - small constant strength reduction
   - loop-invariant provider lookup hoisting
   - table placement in readonly/static storage when native-safe
   - branchless select and constant-time compare preservation
4. Add backend-specific hooks:
   - Cranelift inline fast paths for typed bytes and fixed buffers
   - LLVM canonical IR with target datalayout, attributes only when proven, and
     standard `default<O2/O3>` pipelines
   - optional target intrinsics only behind capability facts
5. Refuse completion when a pure Simple replacement is below target and the
   delta is not tied to an IR/ASM difference.

Performance gates:

- Initial floor: pure Simple native must reach at least `0.80x` portable C for
  new replacements before defaulting on hosted systems.
- Completion target: pure Simple native must reach `1.00x` portable C for hot
  paths, or have an accepted hardware/standalone reason with a named follow-up.
- SFFI provider remains available only as explicit `provider=c` or
  `provider=host`.

## Phase 4 - Hardware-Friendly Simple HAL

Hardware access should be pure Simple where the target allows it.

1. Define typed HAL capsules:
   - `MmioAddress`, `PhysAddress`, `DmaAddress`, `IrqLine`, `RegisterWidth`
   - volatile read/write operations with explicit ordering
   - memory barriers and cache maintenance hooks
   - DMA buffer ownership and alignment contracts
   - interrupt registration and acknowledgement
2. Add target backends:
   - hosted mock backend for tests
   - QEMU backend for reproducible smoke
   - real-board backend for RA4M1/STM32U585/RISC-V boards
   - SFFI backend only for host adapters such as OpenOCD/libusb when needed
3. Keep unsafe hardware operations inside HAL capsules:
   - no arbitrary pointer math in application code
   - no untyped register access outside driver internals
   - no hidden sleep/retry shell-outs in hot request paths
4. Optimize slow hardware paths by fixing:
   - MMIO volatile lowering
   - register bitfield packing
   - polling-loop bounds and timeout lowering
   - DMA copy/coherency paths
   - interrupt dispatch tables

Exit evidence:

- QEMU Simple HAL smoke with real MMIO register interaction.
- Real-board smoke with UART, GPIO, timer, and one storage or DMA path where
  hardware is available.
- Hardware access does not require libc in standalone mode.

## Phase 5 - Fully Standalone Build Mode

Add a `standalone-simple` build profile:

1. No libc, no libm, no pthreads, no shell.
2. Linker script selected by target.
3. Startup, panic, allocation, time, terminal/UART, and memory primitives come
   from pure Simple or a tiny target capsule.
4. Host C libraries can be accessed only in hosted profiles through SFFI.
5. Build metadata records:
   - runtime family
   - provider choices
   - C/SFFI symbols linked
   - hardware target
   - optimization profile

Exit evidence:

- `standalone-simple` hello, memory, string, FAT/NVFS smoke, and UART smoke.
- Symbol audit proves no accidental libc or host C dependency.
- QEMU boot and real-board smoke use the same Simple library code where
  practical.

## Phase 6 - Verification Matrix

Required checks for each migrated library:

- Correctness parity against C/SFFI baseline.
- Native benchmark against portable C.
- Provider-selection test proving pure default and explicit SFFI override.
- No fallback success if provider is unavailable.
- Static symbol audit for standalone builds.
- IR/ASM diff note for every hot path below target.
- Hardware smoke if the library touches MMIO, DMA, IRQ, storage, time, UART, or
  board startup.

Required reports:

- `doc/10_metrics/pure_simple_lib/<date>.sdn`
- `doc/09_report/verify/pure_simple_lib_standalone_<date>.md`
- Updated benchmark ledger in `doc/03_plan/port_rust_c_to_pure_simple.md`

## Work Packages

1. Inventory and benchmark harness owner:
   - module classification
   - C/SFFI/Simple benchmark ledger
   - provider metadata format
2. SFFI/provider owner:
   - typed provider contracts
   - custom primitive ABI mapping
   - availability/version/error probes
3. Pure library owner:
   - memory/string/filesystem/compression/crypto/database ports
   - parity tests
4. Optimization plugin owner:
   - `CLibParityHotspot`
   - C baseline ratio facts
   - MIR/backend transforms
   - IR/ASM delta reports
5. Hardware/standalone owner:
   - typed HAL
   - volatile/MMIO/DMA lowering
   - QEMU and board smoke
   - no-libc symbol audit

## Done Criteria

- New `src/lib` default implementations are pure Simple.
- Hosted C libraries remain accessible through explicit SFFI providers.
- Hot pure Simple paths meet or exceed portable C, or have a measured compiler
  delta and active optimization-plugin task.
- Standalone Simple builds run without libc or host shell.
- QEMU and at least one real board prove hardware access through Simple HAL.
- No dummy, stub, shell, C, Rust, or SFFI fallback can satisfy acceptance
  without being reported as the selected provider.
