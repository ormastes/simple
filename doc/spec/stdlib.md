# Simple Standard Library Specification

## 1. Goals and Scope

The Simple standard library ("stdlib") is designed to:

1. Support multiple runtime variants:
   - Concurrency: async vs sync
   - Memory: gc vs no_gc
   - Platform: host (OS), baremetal, gpu (device)

2. Provide a shared core that is usable across all variants.

3. Allow platform-specific overlays (host/baremetal/gpu) without leaking them into other environments.

4. Expose practical modules: collections, I/O, networking, time, concurrency, JSON, logging, reflection, DSL helpers.

5. Provide command-line argument, environment variable, and configuration management on supported platforms.

6. **Use semantic types exclusively** - no bare primitives in public APIs.

The stdlib is organized as a set of directories under a logical `std` root, plus a variant-aware import resolution mechanism.

### Type Safety Policy

The standard library enforces strict type safety through its root `__init__.spl`:

```simple
# std/__init__.spl
#[deny(primitive_api)]
#[deny(bare_string)]
#[deny(bare_bool)]
mod std

pub mod core
pub mod units
pub mod io
pub mod net
# ... all child modules inherit the deny settings
```

This means:
- All stdlib public APIs use unit types, enums, and `Option<T>`
- No bare `i32`, `i64`, `f64` in public function signatures
- No bare `str`/`String` - use `FilePath`, `Url`, `IpAddr`, etc.
- No bare `bool` - use semantic enums
- Implicit `nil` is always forbidden (must use `Option<T>`)
- Lint enforcement propagates through `__init__.spl` attribute inheritance

**Standard Unit Type Suffixes:**

| Category | Types | Suffixes |
|----------|-------|----------|
| Files | FilePath, FileName, FileExt, DirPath | `_file`, `_filename`, `_ext`, `_dir` |
| Network | IpAddr, Port, SocketAddr, MacAddr | `_ip`, `_port`, `_sock`, `_mac` |
| URLs | Url, HttpUrl, FtpUrl, Host | `_url`, `_http`, `_ftp`, `_host` |
| IDs | UserId, SessionId, etc. | `_uid`, `_sid`, etc. |
| Size | ByteCount, kb, mb, gb | `_bytes`, `_kb`, `_mb`, `_gb` |

See [Unit Types](units.md) for the complete specification.

---

## 2. Variant Model

### 2.1 Axes

Three orthogonal axes define how a compilation unit is built:

1. **Platform axis**
   - `platform_host` - Programs running under an OS (Linux, Windows, etc.)
   - `platform_baremetal` - Programs running without an OS (MCU firmware, kernels, bootloaders)
   - `platform_gpu` - Device-side GPU kernels and related code

2. **Concurrency axis**
   - `async` - Asynchronous runtime, non-blocking I/O, async tasks
   - `sync` - Synchronous (blocking) execution model

3. **Memory axis**
   - `gc` - Garbage-collected heap available
   - `no_gc` - No garbage collector; only stack, static, or explicit arenas/pools

### 2.2 Effective Variant

The effective variant of a compilation unit is the combination:

```
(platform, concurrency, memory, mutability)
```

Some common combinations are named:

| Name | Definition |
|------|------------|
| `host_async_gc` | (platform_host, async, gc) |
| `host_async_nogc` | (platform_host, async, no_gc) - **DEFAULT** |
| `host_sync_gc` | (platform_host, sync, gc) |
| `host_sync_nogc` | (platform_host, sync, no_gc) |
| `bare_async_nogc` | (platform_baremetal, async, no_gc) - **DEFAULT for baremetal** |
| `bare_sync_nogc` | (platform_baremetal, sync, no_gc) |
| `gpu_kernel` | (platform_gpu, async, no_gc) + role gpu_kernel - **DEFAULT for GPU kernels** |
| `gpu_kernel_sync` | (platform_gpu, sync, no_gc) + role gpu_kernel |
| `gpu_host_async_nogc` | (platform_host, async, no_gc) for GPU host-side helpers - **DEFAULT** |
| `gpu_host_async_gc` | (platform_host, async, gc) for GPU host-side helpers |

### 2.3 Attributes

The following attributes participate in variant selection:

- `#[platform_host]`, `#[platform_baremetal]`, `#[platform_gpu]`
- `#[async]`, `#[sync]`
- `#[gc]`, `#[no_gc]`
- `#[mutable]`, `#[immutable]` (mutability mode)
- Optional: `#[strong]` (language safety mode)
- Optional: `#[gpu_kernel]` (marks device-side GPU kernels)

#### 2.3.1 Mutability Modes

| Attribute | Description |
|-----------|-------------|
| `#[mutable]` | Default. Variables are mutable unless declared `let` |
| `#[immutable]` | Variables are immutable by default, use `var` for mutable |

The `#[immutable]` attribute is recommended for:
- Functional programming style
- GPU kernels (reduces synchronization complexity)
- Concurrent code (safer data sharing)

If multiple attributes conflict (e.g. both `#[async]` and `#[sync]`), compilation fails.

#### 2.3.2 Immutable Interface Design Patterns

When designing APIs for immutable modules (`#[immutable]`), follow these patterns:

**Mutable vs Immutable Method Signatures:**

| Operation | Mutable Pattern | Immutable Pattern |
|-----------|-----------------|-------------------|
| Append | `fn push(self, v: T) -> bool` | `fn push(self, v: T) -> Option<Self>` |
| Remove | `fn pop(self) -> Option<T>` | `fn pop(self) -> Option<(T, Self)>` |
| Update | `fn set(self, i: u64, v: T)` | `fn with(self, i: u64, v: T) -> Self` |
| Clear | `fn clear(self)` | `fn cleared() -> Self` |
| Sort | `fn sort(self)` | `fn sorted(self) -> Self` |

**Example - Mutable API (core_nogc/fixed_vec.spl):**
```simple
# Mutates in-place, returns success indicator
pub fn push(self, value: T) -> bool:
    if self.len >= N:
        return false
    self.data[self.len] = value
    self.len = self.len + 1
    return true
```

**Example - Immutable API (core_nogc_immut/static_vec.spl):**
```simple
# Returns new vector with element appended
fn push(self, val: T) -> Option<StaticVec<T, N>>:
    if self._len < N:
        var new_data = self._data
        new_data[self._len] = val
        Some(StaticVec { _data: new_data, _len: self._len + 1 })
    else:
        None
```

**Persistent Data Structures (core_immut/persistent.spl):**

For GC-enabled immutable modules, use structural sharing:
```simple
enum List<T>:
    Nil
    Cons(T, Box<List<T>>)

fn prepend(self, x: T) -> List<T>:
    List.Cons(x, Box.new(self))  # Reuses existing list
```

**Guidelines:**
1. Immutable methods return new instances; original remains unchanged
2. Use `Option<Self>` for operations that may fail (capacity exceeded)
3. Use tuples `(extracted_value, new_collection)` for pop-like operations
4. Prefer verbs ending in `-ed` for transformation methods: `sorted`, `filtered`, `mapped`
5. Use `with_*` prefix for update methods: `with_element`, `with_capacity`

See [Immutable Interface Design Research](../research/immutable_interface_design.md) for detailed patterns.

### 2.4 Profiles (simple.toml)

Profiles define build-level defaults:

```toml
[profiles.default]
# Default: async + no_gc for predictable performance
attributes = ["platform_host", "async", "no_gc", "strong"]
imports   = ["std.*"]

[profiles.server]
# Server applications: async + no_gc (no GC pauses)
attributes = ["platform_host", "async", "no_gc", "strong"]
imports   = ["std.*", "std.net.*"]

[profiles.app]
# Desktop/GUI applications: async + gc (convenience)
attributes = ["platform_host", "async", "gc", "strong"]
imports   = ["std.*"]

[profiles.functional]
# Functional programming: async + gc + immutable
attributes = ["platform_host", "async", "gc", "strong", "immutable"]
imports   = ["std.*", "std.core_immut.*"]

[profiles.cli]
attributes = ["platform_host", "sync", "no_gc", "strong"]
imports   = ["std.*"]

[profiles.baremetal]
# Baremetal: async + no_gc (cooperative scheduling, no OS)
attributes = ["platform_baremetal", "async", "no_gc", "strong"]
imports   = ["std.*"]

[profiles.baremetal_sync]
# Baremetal with blocking execution
attributes = ["platform_baremetal", "sync", "no_gc", "strong"]
imports   = ["std.*"]

[profiles.gpu_kernel]
# GPU kernels: async + no_gc + immutable (default)
attributes = ["platform_gpu", "async", "no_gc", "strong", "gpu_kernel", "immutable"]
imports   = ["std.gpu.kernel.*"]

[profiles.gpu_kernel_sync]
# GPU kernels with sync execution
attributes = ["platform_gpu", "sync", "no_gc", "strong", "gpu_kernel"]
imports   = ["std.gpu.kernel.*"]

[profiles.gpu_host]
# GPU host-side: async + no_gc (default)
attributes = ["platform_host", "async", "no_gc", "strong"]
imports   = ["std.*", "std.gpu.host.*"]

[profiles.gpu_host_gc]
# GPU host-side with GC (convenience)
attributes = ["platform_host", "async", "gc", "strong"]
imports   = ["std.*", "std.gpu.host.*"]
```

**Rules:**
- If profile omits platform, default is `platform_host`
- If profile omits concurrency, default is `async`
- If profile omits memory, default is `no_gc` (**changed from gc**)
- If no profile and no attributes, effective variant is `host_async_nogc`

**Rationale for `no_gc` default:**
- Predictable performance (no GC pauses)
- Lower memory overhead
- Libraries written for `no_gc` work in `gc` contexts (not vice versa)
- Better for servers, embedded, and real-time applications
- Explicit memory management encourages better design

---

## 3. Project Directory Structure

> **Note:** The actual implementation path is `simple/std_lib/src/` rather than the
> originally planned `lib/std/`. This document reflects the actual implementation.

The Simple language project uses the following directory structure:

```
simple/
├── std_lib/src/            # Simple standard library (written in Simple)
│   ├── __init__.spl        # #[deny(primitive_api, bare_string, bare_bool)] mod std
│   ├── core/               # variant-agnostic pure core
│   ├── core_nogc/          # variant-agnostic, explicit #[no_gc]
│   ├── core_immut/         # variant-agnostic, explicit #[immutable]
│   ├── core_nogc_immut/    # #[no_gc] + #[immutable]
│   ├── simd/               # cross-platform SIMD & vector math
│   ├── sys/                # system utilities (args, env)
│   ├── host/               # OS-based stdlib overlays
│   │   ├── async_nogc_mut/ # DEFAULT
│   │   ├── async_gc_mut/
│   │   ├── async_gc_immut/
│   │   └── sync_nogc_mut/
│   ├── bare/               # baremetal stdlib (flat structure)
│   │   ├── hal/            # Hardware abstraction
│   │   ├── io/             # Basic I/O
│   │   ├── async/          # Async executor
│   │   ├── startup.spl
│   │   ├── time.spl
│   │   └── mem.spl
│   ├── gpu/                # GPU device & host APIs
│   │   ├── kernel/         # Device-side (flat structure)
│   │   └── host/
│   │       └── async_nogc_mut/
│   ├── tooling/            # diagnostics, testing, reflection
│   │
│   │   # Platform-specific modules
│   ├── browser/            # Web browser APIs
│   ├── electron/           # Electron desktop
│   ├── godot/              # Godot engine
│   ├── unreal/             # Unreal engine
│   ├── vscode/             # VSCode extension
│   ├── graphics/           # Graphics rendering
│   ├── ml/                 # Machine learning
│   ├── physics/            # Physics simulation
│   └── web/                # Web utilities
│
├── native_lib/             # Native implementations (written in Rust)
│   ├── core/               # Core runtime support
│   │   ├── memory.rs       # Memory allocation, GC interface
│   │   ├── string.rs       # String operations
│   │   └── math.rs         # Math intrinsics
│   ├── io/                 # I/O system interface
│   │   ├── fs.rs           # Filesystem operations
│   │   ├── net.rs          # Network operations
│   │   └── term.rs         # Terminal I/O
│   ├── sys/                # System interface
│   │   ├── args.rs         # Command-line arguments
│   │   ├── env.rs          # Environment variables
│   │   ├── process.rs      # Process management
│   │   └── time.rs         # Time and clocks
│   ├── sync/               # Synchronization primitives
│   │   ├── mutex.rs        # Mutexes and locks
│   │   ├── channel.rs      # Channels
│   │   └── atomic.rs       # Atomic operations
│   └── ffi/                # FFI bridge
│       ├── mod.rs          # FFI entry points
│       └── types.rs        # Type conversions
│
└── src/                    # Compiler implementation (Rust)
    ├── common/             # Shared contracts
    ├── parser/             # Lexer, Parser, AST
    ├── type/               # Type checker
    ├── compiler/           # HIR, MIR, Codegen
    ├── runtime/            # GC, concurrency runtime
    ├── loader/             # SMF binary loader
    ├── pkg/                # Package manager
    └── driver/             # CLI runner
```

### Directory Naming Conventions

| Directory | Purpose | Language |
|-----------|---------|----------|
| `simple/std_lib/src/` | Standard library | Simple |
| `native_lib/` | Native system interface | Rust |
| `src/` | Compiler implementation | Rust |

### Stdlib Directory Layout (`simple/std_lib/src/`)

```
simple/std_lib/src/
├── __init__.spl        # Root manifest with #[deny(primitive_api, bare_string, bare_bool)]
├── prelude.spl         # Auto-imported into every file
├── core/               # Variant-agnostic pure core (mutable default)
│   ├── __init__.spl
│   ├── option.spl
│   ├── result.spl
│   ├── traits.spl
│   ├── math.spl        # Mathematical functions
│   ├── iter.spl        # Iterator utilities
│   ├── cmp_ord.spl     # Comparison and ordering
│   ├── error.spl       # Error trait
│   ├── fmt.spl         # Formatting trait
│   └── graph.spl       # Graph data structure
├── core_immut/         # Variant-agnostic, explicit #[immutable]
│   ├── __init__.spl
│   └── functional.spl  # compose, curry, flip, identity
├── core_nogc/          # Variant-agnostic, explicit #[no_gc] (mutable)
│   ├── __init__.spl
│   ├── arena.spl
│   ├── bump.spl
│   ├── fixed_vec.spl
│   ├── fixed_string.spl
│   ├── small_vec.spl   # Small-buffer optimized vector
│   ├── small_map.spl   # Static maps/dictionaries
│   └── string_view.spl # Borrowed read-only string view
├── core_nogc_immut/    # Variant-agnostic, #[no_gc] + #[immutable]
│   ├── __init__.spl
│   ├── functional.spl  # pure functions (stack-only)
│   └── static_vec.spl  # immutable API fixed-capacity vector
├── units/              # Unit type definitions
│   ├── __init__.spl
│   ├── ids.spl
│   ├── file.spl
│   ├── net.spl
│   ├── url.spl
│   ├── size.spl
│   └── time.spl
├── simd/               # Cross-platform SIMD & vector math
│   ├── __init__.spl
│   ├── types.spl       # Vector types (Vec2, Vec4, Vec8, Vec16)
│   ├── ops.spl         # Vector operations
│   └── intrinsics.spl  # Platform intrinsics
├── sys/                # System utilities
│   ├── args.spl        # Command-line arguments
│   └── env.spl         # Environment variables
├── host/               # OS-based stdlib overlays
│   ├── async_nogc_mut/     # DEFAULT: async + no_gc + mutable
│   │   └── (I/O, networking modules)
│   ├── async_gc_mut/       # async + gc + mutable
│   ├── async_gc_immut/     # async + gc + immutable (functional style)
│   ├── sync_nogc_mut/      # blocking + no_gc + mutable
│   └── common/             # Shared utilities across variants
├── bare/               # Baremetal (single variant: async + nogc + immutable)
│   ├── __init__.spl    # #[variant(platform_baremetal, async, no_gc, immutable)]
│   ├── hal/
│   │   ├── __init__.spl
│   │   ├── gpio.spl
│   │   ├── uart.spl
│   │   ├── timer.spl
│   │   ├── spi.spl
│   │   └── i2c.spl
│   ├── io/
│   │   ├── __init__.spl
│   │   └── serial.spl
│   ├── time.spl
│   ├── mem.spl
│   └── async/
│       ├── __init__.spl
│       ├── executor.spl
│       └── waker.spl
├── gpu/                # GPU APIs
│   ├── kernel/         # Device-side (single variant: async + nogc + immutable)
│   │   ├── __init__.spl    # #[gpu_kernel, immutable]
│   │   ├── core.spl        # thread/block/grid indices
│   │   ├── memory.spl      # global/shared/local access
│   │   ├── simd.spl        # GPU-adapted SIMD
│   │   ├── math.spl        # fast math, fused ops
│   │   ├── atomics.spl     # device atomics
│   │   └── reduce.spl      # warp/block reductions
│   └── host/           # Host-side control
│       └── async_nogc_mut/     # DEFAULT: async + no_gc + mutable
├── tooling/            # Diagnostics, testing, reflection
│   └── __init__.spl
│
│   # Platform-specific modules (domain bindings)
├── browser/            # Web browser APIs
├── electron/           # Electron desktop framework
├── godot/              # Godot game engine
├── unreal/             # Unreal engine
├── vscode/             # VSCode extension APIs
├── graphics/           # Graphics rendering
├── ml/                 # Machine learning
├── physics/            # Physics simulation
├── web/                # Web framework utilities
├── cli/                # CLI utilities
├── doctest/            # Documentation testing
├── mcp/                # Model Context Protocol
└── ui/                 # UI framework
```

**Variant Naming Convention:**
- Format: `{concurrency}_{memory}_{mutability}`
- Example: `async_nogc_mut` = async + no_gc + mutable
- Single variant folders: no suffix needed, config in `__init__.spl`

**Default Variants by Platform:**
| Platform | Default Variant | Rationale |
|----------|-----------------|-----------|
| host | `async_nogc_mut` | Async I/O, predictable memory, mutable for typical apps |
| bare | (single) `async_nogc_immut` | Interrupt-driven, no heap, immutable for safety |
| gpu/kernel | (single) `async_nogc_immut` | Parallel execution, immutable for race-freedom |
| gpu/host | `async_nogc_mut` | Async GPU control, mutable for buffer management |

### Native Library (`native_lib/`)

The `native_lib/` directory contains Rust implementations of system-level functionality that cannot be written in pure Simple:

| Module | Purpose |
|--------|---------|
| `native_lib/core/` | Memory allocation, GC interface, math intrinsics |
| `native_lib/io/` | Filesystem, networking, terminal I/O |
| `native_lib/sys/` | Args, env, process, time |
| `native_lib/sync/` | Mutexes, channels, atomics |
| `native_lib/ffi/` | FFI bridge and type conversions |

**Integration:** Simple stdlib modules in `lib/std/` call into `native_lib/` through `extern` declarations:

```simple
# lib/std/host/async_gc/io/fs.spl
extern fn native_read_file(path: &str) -> Result<Bytes, IoError>
extern fn native_write_file(path: &str, data: &Bytes) -> Result<(), IoError>

pub fn read_file(path: FilePath) -> Result<Bytes, IoError>:
    return native_read_file(path.as_str())
```

---

### 3.1 lib/std/core - Common Backbone

Modules:
- `std.core.primitives`
- `std.core.option_result`
- `std.core.iter`
- `std.core.cmp_ord`
- `std.core.math`
- `std.core.error`
- `std.core.fmt`
- `std.core.traits`

All `lib/std/core` modules MUST either:
- Be annotated `#[variant(any)]`, or
- Satisfy static checks to be safe under all variants (no OS, no GC, no I/O)

### 3.2 lib/std/core_nogc - Strict no-GC Core

Modules:
- `std.core_nogc.arena` - bump/arena allocators and pools
- `std.core_nogc.fixed_vec` - stack/arena bounded vectors
- `std.core_nogc.small_vec` - small-buffer optimized vectors
- `std.core_nogc.small_map` - static maps/dictionaries
- `std.core_nogc.string_view` - borrowed read-only string view

All `lib/std/core_nogc` modules MUST be `#[no_gc]` and `#[variant(any)]`.

### 3.3 lib/std/simd - SIMD / Vector Math

Modules:
- `std.simd.types` - `Simd<T, N>` lane vectors, `Mask<N>` lane masks
- `std.simd.ops` - arithmetic, logical ops, shuffles, blends, reductions
- `std.simd.matrix` - small matrix/vector for graphics/physics (Mat2/3/4, Vec2/3/4)
- `std.simd.intrinsics` - feature detection & hints (SSE/AVX/NEON availability)

Requirements:
- MUST be `#[no_gc]` and platform-agnostic (no OS calls)
- Implementations MAY map to CPU SIMD or GPU native ops depending on platform

---

## 4. Variants by Platform

### 4.1 lib/std/host - OS-based Stdlib

Typical modules (some present only in async_gc or sync_gc):

| Category | Modules |
|----------|---------|
| Data | `collections`, `string`, `regex` |
| I/O | `io.fs`, `io.buf` |
| Network | `net.tcp`, `net.udp`, `net.http_client` |
| System | `time`, `thread`, `sync` (locks, atomics) |
| Async | `async.runtime`, `async.task`, `async.chan`, `async.stream` |
| Utilities | `rand`, `log`, `json` |
| Config | `sys.args`, `sys.env`, `config` |

### 4.2 lib/std/bare - Baremetal Stdlib

**Default variant: `async_nogc`** - Cooperative async scheduling without OS support.

Modules:
- `startup` - reset handler, entry point helpers
- `hal.gpio`, `hal.uart`, `hal.timer`, `hal.spi`, `hal.i2c`
- `io.serial` - basic UART print/read helpers
- `time` - tick-based time (no wall-clock)
- `mem` - volatile memory access, MMIO helpers
- `async.executor` - cooperative single-threaded executor
- `async.waker` - manual waker for interrupt-driven async

**Async Rationale for Baremetal:**
- Interrupt-driven I/O maps naturally to async/await
- Cooperative scheduling without OS threads
- No heap allocation required (stack-based futures)
- Better power efficiency (sleep between events)

All baremetal modules MUST be `#[platform_baremetal, no_gc]`.
Default is `#[async]`; use `#[sync]` for blocking variants.

### 4.3 lib/std/gpu - GPU Kernel + Host GPU Control

#### 4.3.1 std.gpu.kernel.* (device side)

**Default variant: `async_nogc` + `#[immutable]`**

- `std.gpu.kernel.core` - thread/block/grid indices, warp size, lane id
- `std.gpu.kernel.memory` - global/shared/local memory access primitives
- `std.gpu.kernel.simd` - GPU-adapted Simd operations
- `std.gpu.kernel.math` - fast math, fused operations
- `std.gpu.kernel.atomics` - device atomics
- `std.gpu.kernel.reduce` - warp/block reductions, scans

**Async Rationale for GPU Kernels:**
- GPU operations are inherently parallel and asynchronous
- Kernel launches don't block the host thread
- Data transfers happen asynchronously
- Synchronization is explicit (barriers, events)

All MUST be `#[platform_gpu, no_gc, gpu_kernel]`.
Default is `#[async, immutable]`; use `#[sync]` for explicit synchronous kernels.

#### 4.3.2 std.gpu.host.* (host side)

**Default variant: `async_nogc`**

- `std.gpu.host.device` - enumerate devices, query properties
- `std.gpu.host.buffer` - allocate/free device buffers, upload/download
- `std.gpu.host.kernel` - compile/launch kernels, configure grid/block dims
- `std.gpu.host.stream` - async streams/queues; integration with async runtime

**Async Rationale for GPU Host:**
- Non-blocking kernel launches
- Overlapped data transfers
- Integration with host async runtime
- Efficient multi-GPU orchestration

Available variants:
- `async_nogc` - DEFAULT: async + no_gc (predictable performance)
- `async_gc` - async + gc (convenience for scripts)
- `sync_gc` - blocking + gc (simple sequential code)

---

## 5. Variant-Aware Import Resolution

### 5.1 Logical Module Names vs Filesystem

User code imports logical module names:

```simple
use std.io.fs
use std.sys.args
use std.config
use std.gpu.kernel.memory
```

The compiler resolves each logical module name to a concrete file based on the current effective variant.

### 5.2 Resolution Order

Given a logical module path `std.X.Y` and resolution key K, the compiler searches:

1. **Platform + runtime overlay**
   - `lib/std/host/<runtime_key>/X/Y.spl` for platform_host
   - `lib/std/bare/sync_nogc/X/Y.spl` for platform_baremetal
   - `lib/std/gpu/kernel/sync_nogc/X/Y.spl` for platform_gpu with gpu_kernel
   - `lib/std/gpu/host/<runtime_key>/X/Y.spl` for platform_gpu host-side

2. **Platform-only overlay** (optional intermediate level)

3. **Root std module** - `lib/std/X/Y.spl`

4. **Core modules** - `lib/std/core/X/Y.spl`, then `lib/std/core_nogc/X/Y.spl`

If no candidate is found:
```
error: std.X.Y is not available for variant <K>
```

### 5.3 Module #[variant] Attribute

```simple
#[variant(any)]
mod std.core.math

#[variant(host_async_gc)]
mod std.host.async_gc.io.fs

#[variant(bare_sync_nogc)]
mod std.bare.sync_nogc.hal.uart
```

---

## 6. Command-line, Environment, and Configuration

### 6.1 std.sys.args - Command-line Arguments

```simple
/// Returns all command-line arguments excluding the program name.
fn args() -> CmdArgs

/// Returns the program name, if available.
fn program_name() -> Option<String>

/// Convenience: collects arguments to an array.
fn args_list() -> Array<String>
```

### 6.2 std.sys.env - Environment Variables

```simple
/// Returns the current value of an environment variable.
fn get(key: &str) -> Option<String>

/// Sets or overrides an environment variable.
fn set(key: &str, value: &str) -> Result<(), VarError>

/// Removes an environment variable.
fn remove(key: &str) -> Result<bool, VarError>

/// Returns an iterator over (key, value) pairs.
fn vars() -> Iterator<(String, String)>
```

### 6.3 std.config - Configuration Management

Provides a unified way to read configuration from:
- Command-line arguments (`std.sys.args`)
- Environment variables (`std.sys.env`)
- Configuration files (JSON/TOML/YAML)
- In-memory programmatic configuration (for tests)

```simple
/// Immutable configuration tree.
struct Config

/// Builder for composing multiple sources with precedence.
struct ConfigBuilder:
    fn new() -> ConfigBuilder
    fn add_source(self, source: Box<dyn ConfigSource>) -> ConfigBuilder
    fn build(self) -> Result<Config, ConfigError>

/// Accessing values
impl Config:
    fn get_bool(self, path: &str) -> Result<Bool, ConfigError>
    fn get_int(self, path: &str) -> Result<Int, ConfigError>
    fn get_string(self, path: &str) -> Result<String, ConfigError>
    fn get_int_or(self, path: &str, default: Int) -> Int
```

**Built-in sources:**
- `EnvSource` - load from environment variables with prefix
- `ArgSource` - load from command-line arguments
- `JsonFileSource` - load from JSON file
- `MapSource` - load from in-memory map

**Example:**

```simple
use std.config

fn load_server_config() -> Result<Config, ConfigError>:
    ConfigBuilder::new()
        .add_source(Box::new(JsonFileSource { path: "config.json" }))
        .add_source(Box::new(EnvSource { prefix: "APP_", separator: "__" }))
        .add_source(Box::new(ArgSource { ignore_unknown: true }))
        .build()

fn main() -> Int:
    let cfg = load_server_config().unwrap()
    let port = cfg.get_int_or("server.port", 8080)
    0
```

---

## 7. Invariants & Errors

1. **Variant Safety** - No module compiled under variant K may import a stdlib module whose effective variant conflicts with K.

2. **Core Neutrality** - `std.core` and `std.core_nogc` MUST NOT contain platform-specific or GC-requiring operations.

3. **Deterministic Resolution** - For each logical module and variant key, resolution MUST either succeed with exactly one implementation or fail with a clear error.

4. **Host-Only Modules** - Modules like `std.sys.args`, `std.sys.env`, full `std.config` MUST fail cleanly when imported from baremetal or gpu variants.

5. **no_gc Behavior** - Modules used under `no_gc` variants MUST NOT perform hidden heap allocations.

6. **Command-line / Env Stability** - Values returned by `std.sys.args` and `std.sys.env` MUST remain stable for the process lifetime.

7. **Configuration Determinism** - `ConfigBuilder::build()` MUST produce the same `Config` value across runs for identical inputs.

---

## Related Specifications

- [Syntax](syntax.md)
- [Types](types.md)
- [Concurrency](concurrency.md)
- [Memory](memory.md)
