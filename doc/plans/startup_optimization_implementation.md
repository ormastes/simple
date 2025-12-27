# Startup Optimization Implementation Plan

**Created:** 2025-12-28
**Status:** Planned
**Feature Range:** #1970-#1999

## Overview

Implement startup acceleration techniques for Simple Language executables, focusing on:
1. Early argument parsing with mmap child process file prefetching
2. App type specification for resource pre-allocation
3. Binary format extensions for startup hints

## Feature Breakdown

### Phase 1: Early Argument Parsing (#1970-#1976)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1970 | Minimal arg parser stub | 3 | R | Zero-allocation argument parser before runtime init |
| #1971 | Fork-based prefetch child | 3 | R | Fork child process for file prefetching |
| #1972 | mmap + MADV_POPULATE_READ | 2 | R | Memory-map files with read prefetch |
| #1973 | Prefetch file list from args | 2 | R | Extract file paths from command line |
| #1974 | Child process join/wait | 2 | R | Synchronize with prefetch child |
| #1975 | Windows prefetch equivalent | 3 | R | PrefetchVirtualMemory implementation |
| #1976 | Cross-platform abstraction | 2 | R | Unified prefetch API |

**Total: 7 features, Difficulty sum: 17**

### Phase 2: App Type Specification (#1977-#1984)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1977 | App type enum definition | 1 | R | Define cli, tui, gui, service, repl types |
| #1978 | --app-type CLI argument | 2 | R | Parse app type from command line |
| #1979 | @app_type decorator | 2 | S+R | Simple decorator for app type annotation |
| #1980 | SMF header app type field | 2 | R | Add app_type to SMF binary header |
| #1981 | CLI resource pre-allocation | 2 | R | Minimal stdio/heap setup |
| #1982 | TUI resource pre-allocation | 3 | R | Terminal mode, buffers |
| #1983 | GUI window early creation | 4 | R | Create window before runtime init |
| #1984 | Service daemon setup | 3 | R | IPC channels, signal handlers |

**Total: 8 features, Difficulty sum: 19**

### Phase 3: GUI Startup Optimization (#1985-#1991)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1985 | Window hints in SMF header | 2 | R | Store width/height/title in binary |
| #1986 | @window_hints decorator | 2 | S+R | Simple decorator for window config |
| #1987 | Async GPU context init | 4 | R | Background thread for Vulkan init |
| #1988 | Loading indicator display | 3 | R | Show loading UI while init continues |
| #1989 | GPU ready notification | 2 | R | Signal when GPU context is available |
| #1990 | Resource handoff to runtime | 3 | R | Pass pre-created resources to Simple |
| #1991 | Startup progress events | 2 | S+R | Expose startup phases to Simple code |

**Total: 7 features, Difficulty sum: 18**

### Phase 4: Binary Optimizations (#1992-#1999)

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1992 | RELR relocation support | 3 | R | Enable packed relocations in linker |
| #1993 | Symbol stripping profile | 1 | R | Cargo profile for stripped binaries |
| #1994 | LTO optimization profile | 2 | R | Full LTO for release builds |
| #1995 | Section gc configuration | 2 | R | Enable --gc-sections in linker |
| #1996 | Lazy init infrastructure | 3 | S+R | Framework for deferred initialization |
| #1997 | Startup timing metrics | 2 | R | Measure and report startup phases |
| #1998 | Prefetch file manifest | 2 | R | Store prefetch hints in SMF |
| #1999 | Hot path code layout | 4 | R | LTO-driven startup code locality |

**Total: 8 features, Difficulty sum: 19**

## Implementation Summary

| Phase | Features | Difficulty Sum | Est. Lines |
|-------|----------|----------------|------------|
| Phase 1: Early Arg Parsing | 7 | 17 | ~800 |
| Phase 2: App Type Spec | 8 | 19 | ~1,000 |
| Phase 3: GUI Startup | 7 | 18 | ~1,200 |
| Phase 4: Binary Opts | 8 | 19 | ~600 |
| **Total** | **30** | **73** | **~3,600** |

## File Structure

```
src/
├── driver/
│   └── src/
│       ├── early_startup.rs      # Phase 1: Early arg parsing
│       ├── prefetch.rs           # Phase 1: mmap prefetch
│       └── app_type.rs           # Phase 2: App type detection
├── runtime/
│   └── src/
│       └── startup/
│           ├── mod.rs            # Startup module
│           ├── resources.rs      # Phase 2: Resource pre-allocation
│           ├── gui_early.rs      # Phase 3: GUI early init
│           └── metrics.rs        # Phase 4: Timing metrics
├── loader/
│   └── src/
│       └── smf/
│           └── startup_hints.rs  # SMF header extensions
└── compiler/
    └── src/
        └── codegen/
            └── startup_hints.rs  # Emit startup hints to SMF

simple/
└── std_lib/
    └── src/
        └── startup/
            ├── __init__.spl      # Startup module
            ├── app_type.spl      # App type decorators
            └── progress.spl      # Startup progress events
```

## Dependencies

- **Existing:** monoio async runtime, Vulkan GPU backend, SMF loader
- **New:** None (uses existing OS APIs)

## Testing Strategy

1. **Unit tests:** Each phase has isolated unit tests
2. **Benchmark tests:** Measure startup time improvements
3. **Integration tests:** Full startup flow with different app types
4. **Platform tests:** Linux and Windows variants

## Expected Outcomes

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Cold start (CLI) | 100ms | 70ms | 30% |
| Cold start (GUI) | 500ms | 300ms | 40% |
| Hot start (CLI) | 20ms | 15ms | 25% |
| Hot start (GUI) | 100ms | 60ms | 40% |
| Time to first paint (GUI) | 500ms | 150ms | 70% |

## Related Documentation

- [startup_optimization.md](../research/startup_optimization.md) - Research document
- [settlement_and_executable_packaging.md](settlement_and_executable_packaging.md) - Binary format design
- [VULKAN_BACKEND_PLAN.md](VULKAN_BACKEND_PLAN.md) - GPU initialization
