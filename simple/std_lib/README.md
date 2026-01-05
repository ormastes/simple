# Simple Standard Library

This directory contains the Simple language standard library implementation.

## Structure

```
simple/std_lib/
├── src/           # Standard library implementation (.spl files)
│   ├── core/      # Variant-agnostic pure core (mutable)
│   ├── core_immut/     # Variant-agnostic, #[immutable]
│   ├── core_nogc/      # Variant-agnostic, #[no_gc] (mutable)
│   ├── core_nogc_immut/ # Variant-agnostic, #[no_gc] + #[immutable]
│   ├── simd/      # Cross-platform SIMD & vector math
│   ├── host/      # OS-based stdlib overlays (variant-specific)
│   ├── bare/      # Baremetal (single variant: async+nogc+immut)
│   ├── gpu/       # GPU device & host APIs
│   ├── concurrency/ # Concurrency primitives (actors, channels, threads)
│   └── tools/     # Diagnostics, testing, reflection
└── test/          # Standard library tests (.spl files)
    ├── unit/      # Unit tests
    ├── integration/ # Integration tests
    └── fixtures/  # Test fixtures
```

## Variant System

The stdlib supports multiple runtime variants organized by three dimensions:

### 1. Memory Model (GC vs NoGC)

| Directory | GC | Mutable | Description |
|-----------|-----|---------|-------------|
| `core/` | Yes | Yes | Default, garbage collected, mutable |
| `core_immut/` | Yes | No | GC + immutable (persistent data structures) |
| `core_nogc/` | No | Yes | Manual memory (arena, bump, fixed-size) |
| `core_nogc_immut/` | No | No | Static allocation + immutable |

### 2. Async vs Sync

| Variant | Description |
|---------|-------------|
| `async_*` | Non-blocking I/O, futures, async/await |
| `sync_*` | Blocking I/O, traditional threading |

### 3. Host Variants (Combined Profiles)

```
host/
├── async_gc/          # Async + GC
├── async_gc_mut/      # Async + GC + Mutable
├── async_gc_immut/    # Async + GC + Immutable
├── async_nogc_mut/    # Async + NoGC + Mutable (DEFAULT)
├── sync_nogc/         # Sync + NoGC
├── sync_nogc_mut/     # Sync + NoGC + Mutable
└── common/            # Shared implementations
```

### 4. Concurrency Model (Message vs Lock)

| Module | Model | Use Case |
|--------|-------|----------|
| `concurrency/actors.spl` | Message passing | Actor model, isolated state |
| `concurrency/channels.spl` | Message passing | CSP-style, typed channels |
| `concurrency/threads.spl` | Lock-based | Mutex, RwLock, shared state |
| `concurrency/futures.spl` | Async | Works with both models |
| `concurrency/generators.spl` | Coroutines | Lazy sequences, iterators |

## Default Profile

The default profile is **Async + NoGC + Mutable** with message-passing concurrency:

```simple
# From __init__.spl
use host.async_nogc_mut.*
```

This provides:
- Non-blocking async I/O
- Manual memory management (no GC pauses)
- Mutable data structures
- Actor-based concurrency (safe by default)

## Development

The standard library is written in Simple language itself. All `.spl` files in `src/` are compiled and linked into the Simple runtime.

### Testing

Tests are located in `test/` and can be run with:

```bash
simple test simple/std_lib/test/
```

### Documentation

For language specification and design docs, see:
- Main documentation: `simple/doc/` (symlink to `../doc/`)
- Stdlib spec: `simple/doc/spec/stdlib.md`

## Migration Note

**Previous location:** `lib/std/`  
**New location:** `simple/std_lib/src/`

This restructuring creates a `simple/` workspace for Simple language development, separate from the Rust compiler source.

