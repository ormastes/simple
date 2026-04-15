# Startup Optimization for Simple Language

**Last Updated:** 2025-12-28

This document describes startup acceleration techniques for Simple Language executables, covering both Linux (ELF) and Windows (PE/COFF) platforms.

---

## 1) How Executables and Shared Libraries Are Loaded

### Linux (ELF)

The whole executable is **not** read into RAM up front. The kernel loads metadata, sets up an address space, and maps file-backed segments so they are demand-paged.

**High-level sequence:**

1. `execve()` replaces the current process image with the new one.
2. Kernel reads enough of the ELF to locate:
   - `PT_LOAD` segments (code/data) that will be mapped into memory
   - `PT_INTERP` (the dynamic loader, e.g. `ld-linux-x86-64.so.2`) if dynamically linked
3. If there is an interpreter, the kernel starts the dynamic loader first; the loader then maps the main executable and resolves dependencies ("needed" shared objects).
4. Code/data pages are faulted in on demand as execution touches them (minor/major page faults). You can optionally front-load some of those faults with `MAP_POPULATE` (mmap) or `MADV_POPULATE_READ` (madvise).

**Shared libraries (.so):**
Libraries listed in `DT_NEEDED` are typically loaded by the dynamic loader at startup (before main()), though symbol resolution may be lazy by default (PLT lazy binding). You can force "resolve everything at startup" with `LD_BIND_NOW`, but that usually increases startup time while reducing first-call latency.

### Windows (PE/COFF)

Also demand-paged. The loader maps the PE image using section objects; pages come in as needed.

**High-level sequence:**

1. `CreateProcess` creates a new process + initial thread.
2. The image (EXE) is mapped; the loader processes:
   - imports (DLL dependencies)
   - base relocations (for ASLR)
   - TLS callbacks / initializers
3. Implicitly linked DLLs (in the import table) are loaded at process initialization; explicit DLLs are loaded via `LoadLibrary`.
4. Windows supports delay-load: `/DELAYLOAD` changes a DLL so it's loaded on the first call into it, via a helper that calls `LoadLibrary`/`GetProcAddress`.

---

## 2) Where "Cold Start" Time Really Goes

Cold start (after reboot, or when page cache is cold) is dominated by:

1. **I/O + page faults** (reading executable + DSOs + their metadata)
2. **Relocations** (especially for PIE/PIC and ASLR)
3. **Dynamic linking work**
   - locating/loading DSOs
   - symbol resolution/binding strategy
4. **Initializer work**
   - C++ global constructors, Rust runtime init, TLS init
   - heavy work accidentally done before main()

You can't "cheat physics": if the OS has never cached those pages, someone must read them from storage. Most acceleration techniques either (a) reduce the bytes/pages needed, (b) reduce relocation/linker work, or (c) move I/O earlier/more sequentially to reduce random faults.

---

## 3) Startup Acceleration Techniques (Linux + Windows)

### A. Reduce What Must Be Loaded (bytes, pages, dependencies)

**1) Remove dead code and data**
- ELF: `--gc-sections` (plus `-ffunction-sections -fdata-sections`) removes unused sections
- Windows: `/OPT:REF`

**2) Reduce shared-library dependencies**
- ELF: `--as-needed` avoids emitting `DT_NEEDED` for unused libraries

**3) Strip symbols / split debug info**
- Keep debug info out of the runtime image
- Simple: Use release profile with `strip = "symbols"`

### B. Reduce Relocation Cost (often the biggest "loader CPU" win)

**4) Use RELR / packed relative relocations on ELF**
- `DT_RELR` compresses relative relocations, reducing both file size and relocation processing
- Requires glibc 2.36+

**5) Minimize exported symbols and interposition**
- Use visibility settings to hide internal symbols

### C. Defer Work (don't do everything before main)

**6) Delay-load / lazy-load dependencies**
- Windows: `/DELAYLOAD`
- Linux: use `dlopen()` for optional features/plugins

**7) Avoid heavy global initializers**
- Move work from global init to explicit "init" phase after showing UI
- Move to background thread (once the process is already up)

### D. Prefetch / Warm the Cache

**8) Linux prefetch options**
- `mmap(..., MAP_POPULATE)` pre-populates page tables
- `madvise(MADV_POPULATE_READ)` populates readable pages
- `posix_fadvise(..., POSIX_FADV_WILLNEED)` hints to kernel

**9) Windows prefetch**
- `PrefetchVirtualMemory` (Windows 8+) requests address ranges be prefetched

**10) Child process mmap prefetcher**
- A helper process can map EXE + DLLs/DSOs and issue `MAP_POPULATE`/`MADV_POPULATE_READ` to warm caches before the real critical path touches them.

### E. Layout/Locality Tricks

**11) Keep hot startup code/data close together**
- Windows: linker ordering (`/ORDER`)
- Linux: function/data sections plus linker scripts or LTO-driven layout

---

## 4) Simple Language Specific Optimizations

### F. Early Argument Parsing with mmap Child Process

**12) Argparse in Startup Binary with mmap Child Process**

This technique moves argument parsing and file preparation to the very beginning of process startup, before the main runtime initializes.

**How it works:**

```
┌─────────────────────────────────────────────────────────────────┐
│                     Parent Process Startup                       │
├─────────────────────────────────────────────────────────────────┤
│  1. execve() → Minimal stub loader starts                       │
│  2. Parse argv/argc immediately (before any runtime init)       │
│  3. Fork mmap prefetch child process                           │
│  4. Child: mmap + MADV_POPULATE_READ on argument files          │
│  5. Parent: Continue with app type detection                    │
│  6. Child: Warm caches for all input files                     │
│  7. Parent: Begin main runtime initialization                   │
│  8. Join child process (files are now in page cache)           │
└─────────────────────────────────────────────────────────────────┘
```

**Implementation for Simple:**

```simple
# Early startup stub (compiled separately, minimal deps)
extern fn simple_early_startup(argc: i32, argv: **u8) -> AppConfig:
    """
    Called before any Simple runtime initialization.
    Parses args, forks prefetch child, determines app type.
    """
    # 1. Parse command-line arguments (no allocator needed)
    config = parse_args_minimal(argc, argv)

    # 2. Fork child process for file prefetching
    if fork() == 0:
        # Child: mmap and prefetch all input files
        for file in config.input_files:
            fd = open(file, O_RDONLY)
            ptr = mmap(null, file_size(fd), PROT_READ, MAP_PRIVATE | MAP_POPULATE, fd, 0)
            madvise(ptr, file_size(fd), MADV_POPULATE_READ)
            # Keep mapped until exit (warms page cache for parent)
        exit(0)

    # 3. Return config for main process
    return config
```

**Key benefits:**
- File I/O happens in parallel with runtime initialization
- Input files are in page cache when actually needed
- Reduces critical path latency for file-heavy applications

### G. App Type Specification for Resource Pre-allocation

**13) App Type Detection and Resource Pre-allocation**

Simple executables can specify their app type in the binary header or first argument, enabling the loader to pre-allocate appropriate resources.

**App Types:**

| Type | Description | Pre-allocated Resources |
|------|-------------|------------------------|
| `cli` | Command-line tool | Minimal: stdio, basic heap |
| `tui` | Terminal UI app | Terminal mode, input buffer, screen buffer |
| `gui` | Graphical app | Window handle, GPU context, event loop |
| `service` | Background daemon | IPC channels, signal handlers |
| `repl` | Interactive REPL | History buffer, line editor, completion engine |

**Implementation:**

```simple
# In Simple binary header or manifest
@app_type("gui")
@window_hints(width=1280, height=720, title="My App")
fn main():
    # By the time main() runs:
    # - Window is already created (or in progress)
    # - GPU context is being initialized
    # - Event loop thread is spawned
    pass

# Or via command line
# simple --app-type=gui my_app.spl
```

**Early startup sequence with app type:**

```
┌──────────────────────────────────────────────────────────────────┐
│                    App Type Aware Startup                         │
├──────────────────────────────────────────────────────────────────┤
│  1. Read binary header / parse --app-type argument               │
│  2. Fork mmap prefetch child for input files                     │
│  3. Based on app type:                                           │
│     ├─ cli:     Set up stdio, minimal heap                       │
│     ├─ tui:     Enter raw mode, allocate screen buffers          │
│     ├─ gui:     Create window, init GPU context (async)          │
│     ├─ service: Set up IPC, detach from terminal                 │
│     └─ repl:    Init history, line editor                        │
│  4. Continue with Simple runtime initialization                  │
│  5. Join prefetch child                                          │
│  6. Call main() with resources ready                             │
└──────────────────────────────────────────────────────────────────┘
```

**GUI App Specific Optimizations:**

```simple
# For GUI apps, window creation happens BEFORE runtime init
extern fn simple_gui_early_init(config: AppConfig) -> WindowHandle:
    """
    Called immediately after arg parsing, before Simple runtime.
    Creates window and starts GPU initialization in background.
    """
    # Create window immediately (users see something fast)
    window = create_window(
        config.window_hints.width,
        config.window_hints.height,
        config.window_hints.title
    )

    # Start GPU context creation in background thread
    spawn_thread(|| {
        gpu_context = vulkan_init(window)
        set_gpu_ready(gpu_context)
    })

    # Show loading indicator in window
    window.show_loading()

    return window
```

**Benefits:**
- GUI apps show a window within milliseconds
- GPU initialization happens in parallel with runtime setup
- Users perceive faster startup even if total time is same
- Resource allocation matches actual needs (no wasted memory for CLI apps)

---

## 5) Consolidated Startup Acceleration Checklist for Simple

### Priority Order (do first items first):

1. **Measure where startup time goes**
   - page faults / I/O vs relocations vs init code
   - Use `perf record` on Linux, ETW on Windows

2. **Implement early arg parsing + mmap child prefetch** (NEW)
   - Parse args before runtime init
   - Fork child to prefetch input files
   - Join after runtime init

3. **Add app type specification** (NEW)
   - Detect app type from header/args
   - Pre-allocate type-specific resources
   - For GUI: create window before runtime init

4. **Reduce dependencies**
   - ELF: use `--as-needed`
   - Windows: delay-load optional DLLs

5. **Shrink the image**
   - `--gc-sections` on ELF
   - strip symbols

6. **Cut relocation overhead**
   - Enable RELR (`--pack-dyn-relocs=relr`) where supported

7. **Defer work**
   - Move heavy init out of global constructors
   - Use lazy initialization for non-critical subsystems

---

## 6) Simple Compiler Integration Points

### Cargo Profile for Simple Binaries

```toml
# Cargo.toml for Simple compiler/runtime
[profile.release]
opt-level = "z"        # Size optimization
lto = "thin"           # Link-time optimization
codegen-units = 1      # Better optimization
panic = "abort"        # Smaller binary
strip = "symbols"      # Remove debug symbols

[profile.release.package.simple-driver]
# Driver gets extra startup optimization
codegen-units = 1
lto = "fat"            # Full LTO for driver
```

### SMF Binary Format Extensions

The Simple Module Format (SMF) should include:

```rust
// In SMF header
struct SmfHeader {
    magic: [u8; 4],           // "SMF\0"
    version: u32,
    app_type: AppType,        // NEW: cli, tui, gui, service, repl
    window_hints: WindowHints, // NEW: for GUI apps
    prefetch_files: Vec<PathBuf>, // NEW: files to prefetch
    // ... existing fields
}

enum AppType {
    Cli = 0,
    Tui = 1,
    Gui = 2,
    Service = 3,
    Repl = 4,
}
```

---

## 7) Expected Improvements

| Technique | Cold Start Improvement | Hot Start Improvement |
|-----------|----------------------|---------------------|
| mmap child prefetch | 20-40% | 5-10% |
| App type pre-allocation | 15-30% (GUI) | 10-20% (GUI) |
| RELR relocations | 5-15% | 1-5% |
| LTO + strip | 10-20% | 5-10% |
| Lazy initialization | 10-30% | 5-15% |

**Combined effect:** 40-60% cold start improvement for file-heavy GUI applications.

---

## References

- [mold linker documentation](https://github.com/rui314/mold)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [glibc DT_RELR support](https://sourceware.org/git/?p=glibc.git;a=commit;h=4a4b1a3f7d)
- [Windows PrefetchVirtualMemory](https://docs.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-prefetchvirtualmemory)
- [Linux madvise(2)](https://man7.org/linux/man-pages/man2/madvise.2.html)
