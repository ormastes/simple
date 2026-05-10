# SReplay — Simple Replay Debugger Guide

SReplay is a deterministic replay and reverse debugging system for Simple programs, C/C++ programs, baremetal targets, SimpleOS kernel, containers, and VMs. It enables recording program execution and replaying it later with full reverse debugging support.

## Architecture

SReplay is organized into 6 tracks, each addressing a different replay scope:

| Track | Scope | Key Module |
|-------|-------|------------|
| 1 | QEMU full-system replay | `std.replay.qemu_replay` |
| 2 | SimpleOS kernel event log | `os.kernel.replay` |
| 3 | Process-level rr (Linux ptrace) | `std.replay.process` |
| 4 | Simple language semantic trace | `std.replay.semantic` |
| 5 | SimpleOS container checkpoint | `os.kernel.replay.checkpoint` |
| 6 | Simple-native VM replay | `std.replay.vm` |

All tracks share the `ReplayBackend` trait and unified trace format.

## Quick Start

### QEMU Record/Replay (Track 1)

Record a baremetal kernel boot:

```
simple qemu record --arch x86_64 --kernel boot.elf --trace boot.srrq
```

Replay with GDB reverse debugging:

```
simple qemu replay --arch x86_64 --kernel boot.elf --trace boot.srrq
```

Manage checkpoints during replay:

```
simple qemu checkpoint save snap1 --qmp /tmp/qemu-qmp.sock
simple qemu checkpoint restore snap1 --qmp /tmp/qemu-qmp.sock
simple qemu checkpoint list --qmp /tmp/qemu-qmp.sock
```

### Process Recording (Track 3)

Record a Linux process (Simple or C/C++):

```
simple record ./my_app
```

Replay with reverse debugging:

```
simple replay trace.srr
```

### Semantic Trace (Track 4)

Compile with semantic trace instrumentation:

```
simple build --debug-trace=functions   # function enter/exit only
simple build --debug-trace=objects     # + object lifecycle
simple build --debug-trace=full        # + variable writes, borrows, async
```

## Supported Architectures

| Architecture | QEMU System | Baremetal | Machine |
|-------------|-------------|----------|---------|
| x86_64 | `qemu-system-x86_64` | Yes | q35 |
| i386 | `qemu-system-i386` | Yes | q35 |
| aarch64 | `qemu-system-aarch64` | Yes | virt |
| riscv32 | `qemu-system-riscv32` | Yes | virt |
| riscv64 | `qemu-system-riscv64` | Yes | virt |

## Reverse Debugging

SReplay does NOT execute instructions backwards. Instead, reverse execution works by:

1. Finding the nearest checkpoint before the target point
2. Restoring that checkpoint (registers + memory)
3. Replaying forward from the checkpoint to the target event

This approach works across all tracks. GDB MI commands `reverse-step` and `reverse-continue` are supported. DAP `stepBack` and `reverseContinue` are wired for VS Code integration.

## Core Types

### ReplayBackend Trait

All 6 tracks implement the shared `ReplayBackend` trait:

```
trait ReplayBackend:
    fn start_recording(config: ReplayConfig) -> Result<ReplaySessionInfo, text>
    fn start_replay(config: ReplayConfig) -> Result<ReplaySessionInfo, text>
    fn stop() -> Result<Nil, text>
    fn save_checkpoint(name: text) -> Result<text, text>
    fn restore_checkpoint(name: text) -> Result<text, text>
    fn list_checkpoints() -> Result<[text], text>
    fn reverse_step() -> Result<text, text>
    fn reverse_continue() -> Result<text, text>
    fn session_info() -> Option<ReplaySessionInfo>
```

### ReplayConfig

```
struct ReplayConfig:
    arch: Arch
    mode: ReplayMode         # Record or Replay
    kernel_path: text
    trace_path: text
    machine: text
    memory: text
    gdb_port: i32
    qmp_socket: text
    extra_args: [text]
```

### Address (Architecture-Neutral)

Addresses are stored as `u64 + width tag`, never raw pointers:

```
struct Address:
    bits: i32       # 32 or 64
    value: i64      # upper bits zero for 32-bit
```

## Trace File Formats

### QEMU Replay Trace (`.srrq`)

QEMU's native icount-based replay log. Created with `-icount shift=auto,rr=record,rrfile=<path>`.

### Process Replay Trace (`.srr`)

```
trace.srr/
    manifest.sdn          # arch, pointer_width, endianness, event_count
    events.log             # binary ReplayEvent stream
    payloads.bin           # large payloads (file reads, network data)
    checkpoints/
        cp_000001.mem      # register state + dirty pages
    indexes/
        memory_write.idx   # address -> event_id index
        source_line.idx    # source:line -> event_id index
```

### Semantic Trace (`.sst`)

Compiler-injected trace of Simple language-level events: function calls, object lifecycle, ownership transfers, borrow tracking, async task timelines.

### Unified Trace Package (`.sr`)

```
trace.sr/
    manifest.sdn           # SDN metadata: arch, pointer_width, replay mode
    events/
        events-NNNN.slog   # binary event stream (zstd compressed)
    payloads/
        payload-NNNN.bin   # large data (file reads, network, DMA)
    checkpoints/
        cp-NNNNNN/         # register state + memory delta
    indexes/
        memory-write.sidx  # address -> event_id B-tree
        source-line.sidx   # source:line -> event_id
        object-history.sidx
        schedule.sidx
```

## Track Details

### Track 1 — QEMU Full-System Replay

Wraps QEMU's deterministic replay (`-icount shift=auto,rr=record|replay`) for kernel and baremetal reverse debugging. Composes `QemuInstance` + `QmpClient` + `GdbMiClient`.

Key files:
- `src/lib/nogc_sync_mut/replay/qemu_replay.spl` — QemuReplayBackend
- `src/app/qemu/commands.spl` — CLI subcommand implementations
- `src/app/qemu/main.spl` — CLI entry point

### Track 2 — SimpleOS Kernel Event Log

Native kernel replay by logging all nondeterministic events. Zero cost when off (single atomic load + branch).

13 event kinds: ScheduleNext, ThreadCreate, ThreadExit, SyscallEnter, SyscallExit, IrqDeliver, IrqAck, IpcSend, IpcRecv, TimerRead, RandomBytes, MmapResult, DmaTransfer.

Key files:
- `src/os/kernel/replay/hooks.spl` — 11 hook functions called from kernel subsystems
- `src/os/kernel/replay/event_kinds.spl` — EventKind enum + ReplayEntry struct
- `src/os/kernel/replay/log_buffer.spl` — Pre-allocated ring buffer (64K entries)
- `src/os/kernel/replay/divergence.spl` — Replay divergence detection and reporting

### Track 3 — Process-Level rr

`simple record ./app` + `simple replay trace.srr` for Linux host. Works for Simple AND C/C++ programs via ptrace syscall interception.

Key files:
- `src/lib/nogc_sync_mut/replay/process/recorder.spl` — Ptrace-based syscall recorder
- `src/lib/nogc_sync_mut/replay/process/replayer.spl` — Syscall result injection
- `src/lib/nogc_sync_mut/replay/process/checkpoint.spl` — Page-level CoW checkpoints
- `src/lib/nogc_sync_mut/replay/process/chaos_scheduler.spl` — 4 scheduling strategies

Chaos scheduler strategies: RoundRobin, Random, YieldHeavy, StarvationProbe.

### Track 4 — Simple Language Semantic Trace

Compiler-generated debug events via MIR injection (sibling of `mir_aop_injection.spl`).

Instrumentation levels:
- `none` — production (no overhead)
- `functions` — FunctionEnter/Exit (profiling)
- `objects` — + ObjectAlloc/Drop/OwnershipTransfer (memory debugging)
- `full` — + VariableWrite, BorrowStart/End, async events (full replay)

Key files:
- `src/compiler/50.mir/mir_debug_trace_injection.spl` — MIR rewrite pass
- `src/compiler/80.driver/trace_config.spl` — TraceLevel enum + flag parsing
- `src/lib/nogc_sync_mut/replay/semantic/trace_writer.spl` — Runtime trace emitter
- `src/app/debug/replay/semantic_backend.spl` — Debugger overlay

Debugger commands: `show-object`, `show-lifetime`, `show-borrows`, `show-moves`, `reverse-to-field-write`, `show-task`.

### Track 5 — SimpleOS Container Checkpoint/Replay

Snapshot and restore entire SimpleOS containers (process tree, memory, registers, FDs, filesystem, IPC).

Key files:
- `src/os/kernel/replay/checkpoint/container_checkpoint.spl` — Freeze + snapshot orchestration
- `src/os/kernel/replay/checkpoint/container_restore.spl` — Container restore
- `src/lib/nogc_sync_mut/replay/container/checkpoint_format.spl` — Binary `.scc` serialization

### Track 6 — Simple-Native VM Replay

Simple-native VM with deterministic record/replay. RV32I vCPU, virtual memory with dirty page tracking, MMIO device bus.

Devices: Timer, Serial (UART), Block.

Key files:
- `src/lib/nogc_sync_mut/replay/vm/vcpu.spl` — Virtual CPU (RV32I)
- `src/lib/nogc_sync_mut/replay/vm/vmem.spl` — Virtual memory + dirty tracking
- `src/lib/nogc_sync_mut/replay/vm/device_bus.spl` — MMIO dispatch
- `src/lib/nogc_sync_mut/replay/vm/qemu_bridge.spl` — Hybrid QEMU bridge

## Baremetal Replay Core

Low-level replay primitives for baremetal targets (no heap, no GC):

- `bm_replay_set_mode(mode)` — 0=Off, 1=Record, 2=Replay
- `bm_ring_init()` / `bm_ring_push()` / `bm_ring_pop_*()` — Event ring buffer
- `bm_save_checkpoint()` / `bm_restore_checkpoint()` — Checkpoint store
- `bm_find_checkpoint_before(cycle)` — Find nearest checkpoint <= cycle

Location: `src/lib/nogc_async_mut_noalloc/replay/`

## Adapters

Replay adapters bridge the core replay engine to different execution contexts:

| Adapter | File | Purpose |
|---------|------|---------|
| JIT Replay | `adapters/jit_replay.spl` | Record/replay JIT-compiled code |
| Execution Replay | `adapters/execution_replay.spl` | Record/replay interpreter execution |
| QEMU Adapter | `adapters/qemu_replay_adapter.spl` | GDB MI reverse commands via QEMU |
| Remote Replay | `adapters/remote_replay.spl` | Replay over network (GDB remote) |
| Test Runner | `adapters/test_runner_replay.spl` | Replay within test harness |

## Tests

```bash
# Run all replay specs
bin/simple test test/system/replay_baremetal_core_spec.spl
bin/simple test test/system/replay_cli_dispatch_spec.spl
bin/simple test test/system/replay_feature_registry_spec.spl
bin/simple test test/system/replay_divergence_spec.spl
bin/simple test test/system/replay_codec_roundtrip_spec.spl
bin/simple test test/system/replay_semantic_event_spec.spl
bin/simple test test/system/replay_vm_types_spec.spl
bin/simple test test/system/replay_checkpoint_types_spec.spl
bin/simple test test/system/replay_process_event_spec.spl
bin/simple test test/system/replay_chaos_scheduler_spec.spl
```

## 32-bit Architecture Rules

1. Addresses as u64 + width tag — never raw pointers in traces
2. Register schemas by arch — `"riscv32-gpr-v1"`, `"x86_32-v1"`, etc.
3. Event IDs always u64 — no 32-bit overflow risk
4. Page size from manifest — not hardcoded
5. File offsets always i64 — even on 32-bit
6. Object IDs always u64 — avoids exhaustion in long-running programs
7. Guest virtual != physical address — RV32 Sv32 has 32-bit VA but up to 34-bit PA

## Multi-Core Strategy

| Phase | Scope |
|-------|-------|
| A | Single-core deterministic (current) |
| B | Recorded scheduler (multiple threads, single CPU) |
| C | Multi-core deterministic (per-core event streams) |
| D | Chaos scheduler (`simple record --chaos ./app`) |
