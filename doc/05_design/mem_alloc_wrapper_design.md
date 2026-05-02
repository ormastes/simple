# Memory Allocation Wrapper — Design Document

**Date:** 2026-02-22
**Status:** Implemented
**Category:** Infrastructure / Runtime

## Problem

Detecting memory leaks across the interpreter, loader, and native runtime requires:
1. Tracking ALL allocations from a single point
2. Near-zero overhead when not actively detecting leaks
3. Snapshot comparison to identify allocations that were not freed
4. Integration with the test runner to detect leaks during test execution

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│  Simple API (mem_tracker/mod.spl)                       │
│  mem_phase(), mem_diff(), mem_group_by_tag()             │
│  mem_build_report(), mem_print_report()                  │
├─────────────────────────────────────────────────────────┤
│  FFI Bridge (extern fn spl_memtrack_*)                   │
├─────────────────────────────────────────────────────────┤
│  C Runtime (runtime_memtrack.c)                          │
│  Open-addressing hash table, murmur hash, 70% load      │
│  SPL_MALLOC / SPL_FREE / SPL_STRDUP / SPL_REALLOC       │
├─────────────────────────────────────────────────────────┤
│  All runtime allocations                                 │
│  - Strings (str)     - Arrays (arr)    - Dicts (dict)    │
│  - Buffers (buf)     - File I/O (file) - Formatting (fmt)│
│  - Shell output (shell) - User alloc (user)              │
└─────────────────────────────────────────────────────────┘
```

## Zero-Overhead Design

When `g_memtrack_enabled == 0` (default):
- Each `SPL_MALLOC()` call has a single branch `if (g_memtrack_enabled && p)` — predicted not-taken by CPU
- No hash table operations, no counter increments, no memory overhead
- Measured overhead: <1% in benchmarks

When enabled:
- Hash table insert/remove per allocation (~50ns amortized)
- Monotonic alloc_id counter increment per allocation
- Hash table grows at 70% load factor (starts at 4096 entries)

## Snapshot Comparison

```
Phase 0: before-load ──────┐
  (mem_phase("before-load"))│
                            │ diff = leaks from loading
Phase 1: after-load ───────┤
  (mem_phase("after-load")) │
                            │ diff = leaks from test execution
Phase 2: after-tests ──────┤
  (mem_phase("after-tests"))│
                            │ diff = leaks from unloading
Phase 3: after-unload ─────┘
  (mem_phase("after-unload"))

Overall: compare Phase 3 vs Phase 0 = total leaks
```

### API

```simple
# Control
mem_enable()                           # Enable tracking
mem_disable()                          # Disable tracking

# Snapshot
mem_snapshot() -> i64                  # Get monotonic ID
mem_capture_snapshot() -> MemSnapshot  # ID + live_count + live_bytes

# In-memory comparison (no file I/O)
mem_count_since(snap_id) -> i64        # Count live allocs since snapshot
mem_bytes_since(snap_id) -> i64        # Sum bytes since snapshot

# Phase tracking
mem_phase(name) -> MemPhaseSnapshot    # Named snapshot

# Diff (full with entries via file dump)
mem_diff(before, after, dump_path) -> MemDiff
# Diff (fast, no entries, no file I/O)
mem_diff_quick(before, after) -> MemDiff

# Tag grouping
mem_group_by_tag(entries) -> [MemTagGroup]

# Report
mem_build_report(phases, diffs) -> MemLeakReport
mem_print_report(report)
```

### Data Types

```simple
struct MemSnapshot:
    id: i64, live_count: i64, live_bytes: i64

struct MemDiff:
    before_id, before_count, before_bytes: i64
    after_id, after_count, after_bytes: i64
    added_count, added_bytes: i64
    leaked_entries: [MemLeakEntry]

struct MemPhaseSnapshot:
    name: text, snapshot: MemSnapshot

struct MemTagGroup:
    tag: text, count: i64, total_bytes: i64

struct MemLeakReport:
    phases: [MemPhaseSnapshot]
    diffs: [MemDiff]
    tag_groups: [MemTagGroup]
    total_leaked_count, total_leaked_bytes: i64
```

## Test Runner Integration

When `--mem-check` flag is passed or `SIMPLE_MEMTRACK=1` env var is set:

```simple
fn run_tests_with_leak_detection(options, files):
    mem_enable()

    # Phase 0: Before loading
    val p0 = mem_phase("before-load")

    # ... load test files ...

    # Phase 1: After loading
    val p1 = mem_phase("after-load")

    # ... run all tests ...

    # Phase 2: After tests
    val p2 = mem_phase("after-tests")

    # ... unload modules ...

    # Phase 3: After unload
    val p3 = mem_phase("after-unload")

    # Compute diffs
    val load_diff = mem_diff_quick(p0.snapshot, p1.snapshot)
    val test_diff = mem_diff_quick(p1.snapshot, p2.snapshot)
    val unload_diff = mem_diff_quick(p2.snapshot, p3.snapshot)
    val overall_diff = mem_diff(p0.snapshot, p3.snapshot, "/tmp/leak_report.txt")

    # Build and print report
    val report = mem_build_report(
        [p0, p1, p2, p3],
        [load_diff, test_diff, unload_diff, overall_diff]
    )
    mem_print_report(report)
    mem_disable()
```

## Allocation Tags

All runtime allocations carry a tag for post-mortem triage:

| Tag | Source | Typical Count |
|-----|--------|---------------|
| `str` | String allocation/dup | High |
| `arr` | Array struct | Medium |
| `dict` | Dictionary struct | Low |
| `buf` | Read/format buffers | Medium |
| `file` | File I/O buffers | Low |
| `fmt` | Formatting buffers | Low |
| `shell` | Shell command output | Low |
| `user` | User malloc wrapper | Low |

## Coverage

- **Interpreter:** All interpreter-level allocations go through `runtime.c` which uses `SPL_MALLOC` etc.
- **Loader:** Module loading (SMF parsing, symbol table, metadata) uses runtime allocations.
- **Native:** Compiled code calls the same runtime functions for string/array/dict operations.
- **JIT:** JIT compilation uses `mmap`/`munmap` tracked separately by `ResourceLifecycleManager`.

## Files

| File | Purpose |
|------|---------|
| `src/runtime/runtime_memtrack.h` | C API declarations + inline wrappers |
| `src/runtime/runtime_memtrack.c` | Hash table implementation |
| `src/lib/nogc_sync_mut/mem_tracker/types.spl` | Simple type definitions |
| `src/lib/nogc_sync_mut/mem_tracker/mod.spl` | Simple API layer |
| `test/unit/lib/nogc_sync_mut/mem_tracker/mem_tracker_spec.spl` | Core API tests |
| `test/unit/lib/nogc_sync_mut/mem_tracker/mem_diff_spec.spl` | Diff/comparison tests |
| `test/unit/lib/nogc_sync_mut/mem_tracker/mem_phase_spec.spl` | Phase/report tests |
