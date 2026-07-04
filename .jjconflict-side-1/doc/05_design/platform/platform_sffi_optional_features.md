# Platform SFFI and Optional Feature Ports

## 1. Problem: Platform-Dependent Features Need Graceful Degradation

Simple's SFFI layer wraps 1,981+ extern fn declarations across 165+ files. Many
of these target optional or platform-limited hardware:

- **CUDA**: only available on Linux/Windows with NVIDIA hardware
- **Vulkan**: available on Linux/Windows/FreeBSD; partial on macOS (MoltenVK only)
- **Audio** (rodio): may lack sound subsystem on headless servers
- **Window** (winit): unavailable in terminal-only or container environments

Without graceful fallback, calling `cuda_device_count()` on macOS or `audio_init()`
on a headless server crashes or returns garbage. The old pattern was to check
`*_available()` at call site — but this was inconsistent and spread across the codebase.

Additionally, Simple's SFFI I/O layer hardcoded `/bin/sh` for file writes, directory
walks, sleep, and cwd detection — breaking all Windows support.

---

## 2. Decision: Typed Port Pattern (not DiContainer) for Feature Abstraction

Two DI patterns exist in the codebase:

| Pattern | Where | Characteristics |
|---------|-------|-----------------|
| `DiContainer` (string-keyed) | `src/app/` | Flexible, dynamic, no type safety |
| Typed port structs | `src/compiler/compiler_services.spl` | Type-safe, visible graph, no-op defaults |

**Decision: Use typed port structs** (same as CompilerServices) for optional features.

Rationale:
- Compile-time type safety — wrong port type is a type error, not a runtime string miss
- Self-documenting — port fields list the complete contract
- Zero-cost no-op defaults — a noop port is just a struct with `\: false` functions
- No hidden indirection through string keys

---

## 3. Port Hierarchy

Ports are defined in `src/app/io/feature_ports.spl`:

### GpuComputePort
Abstracts CUDA, Vulkan, wgpu, or none:

```simple
struct GpuComputePort:
    name: text
    is_available_fn: fn() -> bool
    device_count_fn: fn() -> i64
    device_name_fn: fn(i64) -> text
    alloc_fn: fn(i64) -> i64
    free_fn: fn(i64) -> bool
    sync_fn: fn() -> bool
```

### AudioPort
Abstracts rodio or none:

```simple
struct AudioPort:
    name: text
    is_available_fn: fn() -> bool
    init_fn: fn() -> i64
    shutdown_fn: fn(i64) -> bool
```

### WindowPort
Abstracts winit or none:

```simple
struct WindowPort:
    name: text
    is_available_fn: fn() -> bool
```

---

## 4. Detection: Runtime `*_available()` Probing

Each SFFI module now exports a standardized `*_available() -> bool` function:

```simple
# Pattern A — extern-backed (for linked-in libraries):
extern fn rt_cuda_is_available() -> bool
fn cuda_available() -> bool:
    rt_cuda_is_available()
```

The C runtime `rt_cuda_is_available()` returns false when CUDA is not installed
(the extern fn stubs to 0). This is **runtime probing**, not compile-time `#ifdef`.

Availability is checked in `feature_registry.spl`'s `init_features()` at startup.

**Platform GPU availability matrix:**

| Platform | CUDA | Vulkan | No-op |
|----------|------|--------|-------|
| Linux + NVIDIA | ✅ primary | ✅ fallback | ✅ |
| Linux + AMD | ❌ | ✅ primary | ✅ |
| macOS | ❌ | ⚠️ MoltenVK | ✅ |
| FreeBSD | ❌ | ⚠️ experimental | ✅ |
| Windows | ✅ NVIDIA only | ✅ | ✅ |

---

## 5. Registration: Module Registry with Noop Defaults

The registry (`src/app/io/feature_registry.spl`) holds module-level vars:

```simple
var _gpu = nil     # set by register_gpu()
var _audio = nil   # set by register_audio()
var _window = nil  # set by register_window()

fn gpu_port() -> GpuComputePort:
    _gpu ?? noop_gpu_port()
```

`noop_gpu_port()` returns a GpuComputePort where:
- `is_available_fn` returns `false`
- `device_count_fn` returns `0`
- `alloc_fn` returns `0` (null pointer)
- `free_fn` / `sync_fn` return `true` (safe no-op)

`init_features()` probes each feature and registers the best available backend:

```simple
fn init_features():
    if cuda_available():
        register_gpu(make_cuda_port())
    elif vulkan_available():
        register_gpu(make_vulkan_port())
    # else: noop_gpu_port is the default
```

---

## 6. Platform Support Matrix for FFI Modules

| Module | Linux | macOS | FreeBSD | OpenBSD | NetBSD | Windows |
|--------|-------|-------|---------|---------|--------|---------|
| `file_ops` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (fixed) |
| `dir_ops` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (fixed) |
| `env_ops` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (fixed) |
| `time_ops` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (fixed) |
| `cuda_ffi` | ✅ NVIDIA | ❌ | ❌ | ❌ | ❌ | ✅ NVIDIA |
| `vulkan_ffi` | ✅ | ⚠️ MoltenVK | ⚠️ | ❌ | ❌ | ✅ |
| `audio_ffi` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `window_ffi` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `http_ffi` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `sqlite_ffi` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `tls_ffi` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `vhdl_ffi` | ✅ (GHDL) | ✅ | ✅ | ✅ | ✅ | ⚠️ |

---

## 7. How to Add a New Optional Feature

1. **Create `src/app/io/<feature>_ffi.spl`** with `extern fn rt_<feature>_is_available() -> bool`
   and `fn <feature>_available() -> bool: rt_<feature>_is_available()`

2. **Add `<feature>_available` as first export** in the new module

3. **Add a port struct** to `src/app/io/feature_ports.spl`:
   ```simple
   struct MyFeaturePort:
       name: text
       is_available_fn: fn() -> bool
       # ... feature-specific fn fields
   ```

4. **Add registry support** to `src/app/io/feature_registry.spl`:
   - `var _myfeature = nil`
   - `fn noop_myfeature_port() -> MyFeaturePort: ...`
   - `fn register_myfeature(port: MyFeaturePort): _myfeature = port`
   - `fn myfeature_port() -> MyFeaturePort: _myfeature ?? noop_myfeature_port()`

5. **Add `make_<feature>_port()`** to the FFI module (imports feature_ports)

6. **Call in `init_features()`** inside feature_registry.spl

7. **Re-export** from `src/app/io/mod.spl`

---

## 8. Windows Cross-Platform Fixes

Before this change, these Simple functions shelled out to `/bin/sh`:

| Function | Old (broken on Windows) | New (cross-platform) |
|----------|------------------------|----------------------|
| `file_write()` | `cat > file` via shell | `rt_file_write()` C call |
| `file_append()` | `cat >> file` via shell | `rt_file_append()` C call |
| `file_atomic_write()` | `mv` via shell | `rt_rename()` C call |
| `rt_file_rename()` | `mv` via shell | `rt_rename()` C call |
| `dir_walk()` | `find -type f` via shell | `rt_dir_walk()` C call |
| `is_dir()` | `test -d` via shell | `rt_is_dir()` C call |
| `dir_list()` | shell listing | `rt_dir_list_array()` C call |
| `cwd()` | `pwd` via shell | `rt_getcwd()` C call |
| `rt_sleep_ms()` | `sleep N` via shell | `rt_sleep_ms_native()` C call |

New C functions added to `src/compiler_src/compiler_seed/platform/unix_common.h` and
`src/compiler_src/compiler_seed/platform/platform_win.h` (Windows counterparts):

- `rt_getcwd()` — `getcwd()` / `GetCurrentDirectoryA()`
- `rt_is_dir()` — `stat()` + `S_ISDIR` / `GetFileAttributesA()`
- `rt_rename()` — `rename()` / `MoveFileA()`
- `rt_sleep_ms_native()` — `nanosleep()` / `Sleep()`
- `rt_env_set()` — `setenv()` / `_putenv_s()`
- `rt_time_now_unix_micros()` — `gettimeofday()` / `GetSystemTimePreciseAsFileTime()`
- `rt_hostname()` — `gethostname()` / `GetComputerNameA()`
- `rt_getpid()` — `getpid()` / `GetCurrentProcessId()`

`rt_dir_walk()` and `rt_dir_list_array()` are in `runtime.c` (they return `SplArray*`
which requires `runtime.h` definitions not available in platform headers).
