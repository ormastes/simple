# Native Runtime Modules — Why-C Research

Analysis of 18 "must-stay-native" C runtime modules in `src/runtime/`.
For each module: what it does, why it must stay C, extractable parts, and
compiler-emission potential.

---

## 1. `runtime.c` (2831 LOC) — Core Runtime

### What it does
The central coordination module. Exports:
- Debug/trace flags: `rt_set_macro_trace`, `rt_set_debug_mode`
- String hash: `rt_str_hash`
- File I/O: `rt_file_read_text`, `rt_file_exists`, `rt_file_write`, `rt_file_append`
- Env vars: `rt_env_get`, `rt_env_get_i64`
- Atomics: `rt_atomic_int_{new,load,store,swap,compare_exchange,fetch_add,...}`, `rt_atomic_bool_*`
- Value boxing: `rt_enum_new`, `rt_enum_discriminant`, `rt_enum_payload`, `rt_enum_check_discriminant`
- BDD test hooks: `rt_bdd_describe_start_rv`, `rt_bdd_it_start_rv`, `rt_bdd_it_end`, `rt_bdd_expect_eq_rv`
- mimalloc allocator integration (`#include "mimalloc.h"`)
- File prefetch via `mmap` + `MADV_POPULATE_READ` (background child process)

### Why must stay C
- **`_Atomic` / `stdatomic.h`**: C11 atomics map directly to CPU atomic instructions; Simple has
  no equivalent language primitive yet.
- **`mmap` / `MADV_POPULATE_READ`**: POSIX-only syscall; requires `sys/mman.h`.
- **mimalloc allocator**: the allocator itself is a C library; the integration point (`SPL_MALLOC`
  macro family) must live in C to intercept all allocation calls globally.
- **Signal-safe initialization** (`_Atomic` global flags): async-signal-safe C11 is required.
- **`dirent.h`**, **`sys/stat.h`**: POSIX filesystem types used inline.

### Extractable to Simple
- `rt_env_get` / `rt_env_get_i64`: logic is trivial (getenv + strtoll); once Simple has a
  `libc.getenv` extern binding, these can move.
- BDD hook functions are pure bookkeeping (counters, string formatting); could become a
  `std.spec.runtime` Simple module that calls a minimal C trampoline for atomic counter updates.
- Debug/trace flag getters/setters: trivially replaceable with `var` globals once Simple supports
  module-level mutable statics.

### Compiler emission potential
Atomic ops can eventually be compiler intrinsics (`@atomic_load`, `@atomic_store`). File I/O
wrappers can become SFFI calls once Simple has a stable syscall layer.

---

## 2. `runtime_native.c` (1558 LOC) — Native Operations

### What it does
Value boxing/unboxing layer (the Simple tagged-value ABI) plus string, array, I/O primitives:
- Value constructors: `rt_value_int`, `rt_value_float`, `rt_value_bool`, `rt_value_nil`
- Core string: `rt_string_new`, `rt_string_len`, `rt_string_data`, `rt_string_concat`,
  `rt_string_char_code_at`, `rt_string_eq`, `rt_text_eq_fast`
- Print/IO: `rt_print`, `rt_println`, `rt_readline`, `rt_stdin_read_line`,
  `rt_stdout_write_text`, `rt_stdout_write`, `rt_stdout_flush`, `rt_stderr_write`,
  `rt_stderr_flush`
- Misc: `rt_len`, `rt_to_string`, `rt_raw_u64_to_string`, `rt_value_to_string`,
  `rt_native_eq`, `rt_native_neq`, `rt_slice`
- Memory: `rt_alloc`, `rt_realloc`, `rt_free`, `rt_memcpy`, `rt_memset`, `rt_memcmp`
- DMA: `rt_dma_alloc`, `rt_dma_free`, `rt_dma_virt_of`, `rt_dma_phys_of`,
  `rt_dma_sync_for_device`, `rt_dma_sync_for_cpu`
- Interpreter hook: `rt_interp_call`, `rt_function_not_found`
- Args: `rt_set_args`, `rt_get_argc`, `rt_get_args`

### Why must stay C
- **Tagged-value ABI** (`int64_t` NaN-boxing for int/float/heap/special): this is the core
  representation contract between the compiler backend and the runtime. Changing it in Simple
  would be circular bootstrapping — the compiler itself relies on these C-level helpers.
- **`rt_interp_call`**: calls back into the interpreter engine (Rust FFI boundary); cannot be
  expressed in Simple without circular dependency.
- **DMA ops** (`rt_dma_alloc`): use `mmap` + `dma_buf` / `/dev/dma_heap` or platform-specific
  DMA APIs; require direct syscall/ioctl access.
- **`rt_memcpy` / `rt_memset` / `rt_memcmp`**: these must be C builtins; the compiler itself
  may lower array copies to them — calling a Simple wrapper would be recursive.

### Extractable to Simple
- `rt_print` / `rt_println` / `rt_readline`: could become thin Simple wrappers over
  `std.io_runtime` FFI, as they are already called from Simple code.
- `rt_to_string` / `rt_value_to_string`: the string-formatting logic (for int, float, bool,
  nil branches) could be expressed in Simple once the tagged-value ABI is stable.

### Compiler emission potential
Low until tagged-value ABI is abstracted away (post-self-hosting). After that, `rt_alloc` /
`rt_free` could become `@alloc` / `@free` intrinsics.

---

## 3. `runtime_thread.c` (613 LOC) — Threading

### What it does
Cross-platform threading and synchronization:
- Threads: `rt_thread_create`, `rt_thread_join`, `rt_thread_detach`, `rt_thread_self`
- Mutexes: `rt_mutex_new`, `rt_mutex_lock`, `rt_mutex_trylock`, `rt_mutex_unlock`,
  `rt_mutex_free`
- Condition variables: `rt_condvar_new`, `rt_condvar_wait`, `rt_condvar_wait_timeout`,
  `rt_condvar_signal`, `rt_condvar_broadcast`, `rt_condvar_free`
- Channels (via mutex + condvar internally)

### Why must stay C
- **`pthread_create` / `pthread_join` / `pthread_detach`**: POSIX thread primitives with C
  callback signatures (`void* (*)(void*)`) — not expressible in Simple.
- **`pthread_mutex_t` / `pthread_cond_t`**: opaque OS types that must be allocated and managed
  by C. Their binary layout is implementation-defined.
- **Windows path** (`#include <windows.h>` / `CreateThread`): dual-platform support via
  conditional compilation — not available in Simple.
- **`pthread_rwlock_t g_handle_rwlock`**: guard for the handle table; must be initialized at
  C link time (`PTHREAD_RWLOCK_INITIALIZER`).

### Extractable to Simple
- Handle table bookkeeping (mapping `int64_t` opaque handles to pointers): could live in Simple
  as a `HashMap<i64, OpaqueHandle>` once the lock is handled by a C primitive.
- Channel queue logic (MPMC queue over condvar): the algorithmic part could be pure Simple;
  only the condvar wait/signal calls stay C.

### Compiler emission potential
None near-term. Eventually, if Simple gets a coroutine/task model, user-space threads can replace
pthreads for most use-cases, reducing this to a thin OS-binding shim.

---

## 4. `runtime_simd_case.c` (422 LOC) — SIMD Case Conversion

### What it does
Fast ASCII case conversion using SIMD:
- `rt_text_is_ascii(value) -> i64`
- `rt_text_to_upper_ascii(value) -> i64`
- `rt_text_to_lower_ascii(value) -> i64`

Implements SSE2 (128-bit) and AVX2 (256-bit) variants selected at runtime via dispatch table.

### Why must stay C
- **`__attribute__((target("sse2")))` / `__attribute__((target("avx2")))`**: GCC/Clang
  per-function ISA targeting; allows the same TU to contain SSE2 and AVX2 functions that are
  linked into one binary and dispatched at runtime. Simple has no equivalent.
- **`__m128i` / `__m256i` types**: Intel intrinsic vector types; not part of any portable ABI.
- **`_mm_loadu_si128`, `_mm_cmpeq_epi8`, `_mm256_movemask_epi8`, etc.**: hardware intrinsics
  that map 1:1 to x86 SSE/AVX instructions.

### Extractable to Simple
- **Scalar fallback path**: all three functions have a byte-by-byte fallback for non-ASCII or
  non-x86 targets. This fallback can be a pure Simple function — the C file could call back into
  it for non-SIMD platforms.
- The dispatch logic (is-ascii check on cached flag) is pure boolean logic that Simple could own.

### Compiler emission potential
High long-term: if the Simple compiler gains a `@simd` / vector type system (similar to
Zig's `@Vector`), these loops can be emitted from Simple source. The dispatch table would
become a compiler-managed capability query.

---

## 5. `runtime_simd_dispatch.c` (52 LOC) — SIMD Dispatch

### What it does
Houses the SIMD dispatch table stubs:
- Scalar stub definitions for `g_simd_crypto` dispatch table.
- The text dispatch table (`g_simd_text`) is initialized in `runtime_simd_utf8.c`.
- Dispatch uses `__builtin_cpu_supports` (GCC/Clang) to pick SSE2 vs AVX2 at first call.

### Why must stay C
- **`__builtin_cpu_supports("avx2")`**: compiler built-in that emits CPUID queries; no Simple
  equivalent.
- **Function pointer dispatch table** with C ABI function pointers: cross-compilation unit
  function pointer tables require C linkage.

### Extractable to Simple
- Nothing: this is pure glue/dispatch infrastructure.

### Compiler emission potential
The dispatch mechanism itself (CPUID + function table) could become a compiler feature:
`@cpu_feature("avx2")` guard blocks.

---

## 6. `runtime_simd_search.c` (599 LOC) — SIMD String Search

### What it does
Substring search and string equality using SIMD:
- `rt_simd_str_search(haystack, needle) -> i64` — forward Boyer-Moore-like with SSE2/AVX2
- `rt_simd_str_last_index_of(haystack, needle) -> i64` — reverse variant
- `rt_simd_str_equal(a, b) -> i64` — fast equality

SSE2 and AVX2 variants selected via dispatch table.

### Why must stay C
Same as `runtime_simd_case.c`: `__attribute__((target))`, `__m128i` / `__m256i`,
`_mm_cmpeq_epi8`, `_mm_movemask_epi8`, `_mm256_*` intrinsics.

### Extractable to Simple
- **Scalar fallback** (naïve substring search): already present as a C fallback; could be
  rewritten in pure Simple and called from the dispatch table when no SIMD is available.

### Compiler emission potential
Same as case conversion — eventual `@Vector` / `@simd` support.

---

## 7. `runtime_simd_utf8.c` (631 LOC) — SIMD UTF-8

### What it does
UTF-8 validation, codepoint counting, and byte classification using SIMD:
- `rt_text_count_codepoints(value) -> i64`
- `rt_text_count_codepoints_cached(value) -> i64`
- `rt_text_validate_utf8(value) -> i64`
- `rt_text_find_invalid_utf8(value) -> i64`

Also owns the `g_simd_text` dispatch table initialization. Contains SSE2 and AVX2 variants for
continuation-byte counting and high-bit detection.

### Why must stay C
- Same SIMD intrinsics rationale as case/search above.
- Additionally owns dispatch table initialization (must run before any string operation).
- `ctype.h` locale-based fallback classification.

### Extractable to Simple
- The cached ASCII flag check (`rt_str_is_ascii_cached`) is a simple struct field read —
  extractable.
- Scalar UTF-8 byte-counting loop: pure algorithm, no intrinsics.

### Compiler emission potential
Moderate. UTF-8 validation could be a `@validate_utf8` compiler intrinsic. Codepoint counting
is a candidate for auto-vectorization if the compiler understands the loop structure.

---

## 8. `runtime_process.c` (273 LOC) — Process Management

### What it does
Subprocess spawning with piped I/O:
- `rt_process_spawn_piped(cmd, args) -> i64` — fork+exec with stdin/stdout pipes
- `rt_process_write_stdin(pid, data) -> bool`
- `rt_process_read_stdout(pid) -> text`
- `rt_process_is_alive(pid) -> bool`
- `rt_editor_spawn_simple_dap()` — spawn DAP debug adapter
- `rt_editor_start_simple_dap`, `rt_editor_poll_simple_dap_stopped`,
  `rt_editor_wait_simple_dap_stopped` — DAP protocol polling

### Why must stay C
- **`fork()` + `execvp()`**: POSIX-only; not expressible in Simple. Fork semantics (copy-on-write
  address space duplication) require OS primitives.
- **`pipe()` + `dup2()` + `fcntl(F_SETFL, O_NONBLOCK)`**: file descriptor wiring at the
  POSIX level.
- **`waitpid(WNOHANG)`**: non-blocking child reaping.
- **`_exit(127)`**: must call `_exit` not `exit` in the child after failed exec.
- Windows stub present but unimplemented: dual-platform compile-time guards.

### Extractable to Simple
- DAP protocol message parsing/formatting (JSON-over-stdio): pure logic that could live in a
  Simple `std.dap` module.
- Argument list construction (C `argv[]` array): the argv-building loop could be Simple if a
  `execvp` extern binding existed.

### Compiler emission potential
None for the syscall layer. The DAP protocol layer above it is entirely extractable.

---

## 9. `runtime_fork.c` (320 LOC) — Fork Operations

### What it does
Test runner isolation via fork:
- `rt_fork_child_setup() -> i64` — `fork()`, wire pipes, return child PID to parent
- `rt_fork_parent_wait(child_pid, timeout_ms) -> i64` — poll pipes, collect stdout/stderr,
  `waitpid` with timeout
- `rt_fork_parent_stdout() -> text`, `rt_fork_parent_stderr() -> text`
- `rt_fork_child_exit(exit_code)` — `_exit()` in child
- Windows stub: returns "fork not supported on Windows"

### Why must stay C
- **`fork()`**: POSIX primitive; no Simple equivalent.
- **`pipe()` + `poll()` + `dup2()`**: low-level FD operations.
- **Signal handler reset in child** (`signal(SIGCHLD, SIG_DFL)`): must run immediately after
  fork, before any C++ or GC teardown.
- **`SPL_REALLOC` growth loop for stdout/stderr capture**: interacts directly with mimalloc.

### Extractable to Simple
- The buffer-draining loop logic (grow buffer, read from FD, null-terminate): algorithmic,
  could be Simple if FD read is an extern.
- Timeout calculation (`clock_gettime` + deadline arithmetic): pure math, extractable.

### Compiler emission potential
None for fork/pipe primitives. Could be abstracted as `@fork()` + `@pipe()` intrinsics in a
future baremetal/OS target.

---

## 10. `async_driver.c` (346 LOC) — Async I/O

### What it does
Unified async I/O facade over platform backends:
- `rt_driver_create(queue_depth) -> i64` — selects epoll / io_uring / kqueue / IOCP
- `rt_driver_submit_{accept,connect,recv,send,sendfile,read,write,open,close,fsync,timeout}`
- `rt_driver_flush`, `rt_driver_poll`, `rt_driver_cancel`
- `rt_driver_poll_id`, `rt_driver_poll_result`, `rt_driver_poll_flags`, `rt_driver_poll_data`,
  `rt_driver_poll_data_len`
- `rt_driver_backend_name`, `rt_driver_supports_sendfile`, `rt_driver_supports_zero_copy`
- Legacy epoll FFI: `rt_epoll_create`, `rt_epoll_ctl`, `rt_epoll_wait`

Platform backends in `src/runtime/platform/`:
- `async_linux_epoll.c` — epoll readiness + completion emulation
- `async_linux_uring.c` — io_uring (true proactor)
- `async_freebsd.c` — kqueue + kernel AIO
- `async_macos.c` — kqueue
- `async_windows.c` — IOCP

### Why must stay C
- **`epoll_create1`, `epoll_ctl`, `epoll_wait`** (Linux): syscall wrappers.
- **`io_uring_setup`, `io_uring_enter`, `io_uring_register`** (Linux 5.1+): requires
  `<linux/io_uring.h>` and direct kernel ring-buffer mapping via `mmap`.
- **`kqueue` / `kevent`** (BSD/macOS): BSD-specific syscalls.
- **`IOCP`** (Windows): `CreateIoCompletionPort` Win32 API.
- Per-platform `#ifdef` selection at compile time.

### Extractable to Simple
- The completion-event demultiplexing logic (event-loop dispatch table): once the raw poll
  results are in a Simple array, all routing logic is pure Simple.
- `rt_driver_backend_name` string map: trivially a Simple `match`.

### Compiler emission potential
None for the syscall level. A Simple `async` runtime (event loop, tasks) could sit atop these
C bindings as a pure Simple scheduler.

---

## 11. `runtime_sdl2.c` (652 LOC) — SDL2 Bindings

### What it does
Thin wrapper over SDL2:
- `rt_sdl2_init`, `rt_sdl2_quit`
- `rt_sdl2_create_window`, `rt_sdl2_destroy_window`, `rt_sdl2_get_window_{width,height}`,
  `rt_sdl2_set_window_title`
- `rt_sdl2_present_rgba` — blit pixel array to screen via `SDL_BlitScaled`
- `rt_sdl2_poll_event` — returns event type int (1=quit, 2=keydown, … 9=textinput)
- Event field accessors: `rt_sdl2_event_key_code`, `rt_sdl2_event_key_sym`,
  `rt_sdl2_event_key_mod`, `rt_sdl2_event_mouse_x/y`, `rt_sdl2_event_text_input`, etc.
- `rt_sdl2_get_ticks`, `rt_sdl2_delay`

### Why must stay C
- **`#include <SDL2/SDL.h>`**: SDL2 is a C library. Its types (`SDL_Window*`, `SDL_Surface*`,
  `SDL_Event`) are C structs accessed via C APIs.
- **Pointer-to-opaque-handle cast** (`(SDL_Window*)(uintptr_t)handle`): requires C-level
  unsafe pointer casting.
- **`SDL_CreateRGBSurfaceFrom`**: takes a raw pixel buffer pointer.

### Extractable to Simple
- **Event enum mapping** (switch on `SDL_EventType` → Simple integer constant): pure mapping,
  could be a Simple `enum` with SFFI.
- **Window title/size logic**: purely delegating to C; once SFFI bindings exist for SDL2
  structs, these could become Simple SFFI wrappers.

### Compiler emission potential
Medium: SDL2 bindings are a candidate for auto-generated SFFI from SDL2 headers.
The pixel-blit loop inside `rt_sdl2_present_rgba` is the only non-trivial logic; it could be
a Simple function once SDL surface access is via SFFI.

---

## 12. `runtime_audio.c` (198 LOC) — Audio

### What it does
miniaudio engine wrapper:
- `rt_audio_init`, `rt_audio_shutdown`
- `rt_audio_load_sound(path) -> handle`, `rt_audio_unload_sound(handle)`
- `rt_audio_play(handle) -> playback_handle`, `rt_audio_play_looped`
- `rt_audio_stop`, `rt_audio_pause`, `rt_audio_resume`
- `rt_audio_set_volume(playback, volume)`, `rt_audio_set_master_volume`,
  `rt_audio_get_master_volume`
- `rt_audio_is_playing(handle) -> i64`
- `rt_audio_set_sound_position` (3D), `rt_audio_set_spatialization_enabled`,
  `rt_audio_set_listener_position`

### Why must stay C
- **`#include "miniaudio.h"` (header-only)**: miniaudio is compiled by including the header in
  a single C TU (`#define MINIAUDIO_IMPLEMENTATION`). It uses OS audio APIs:
  ALSA/PulseAudio (Linux), CoreAudio (macOS), WASAPI (Windows).
- **`ma_engine`, `ma_sound`**: C structs with platform-specific internals.
- **Audio callback thread**: miniaudio spawns a realtime audio callback thread internally;
  only the C calling conventions it uses are guaranteed async-signal-safe.

### Extractable to Simple
- High-level API choreography (load → play → stop lifecycle): pure state machine, could be
  Simple once handles are opaque i64 tokens.
- Volume/spatialization parameter validation: pure math.

### Compiler emission potential
Low. Audio requires OS-level realtime thread priorities and platform audio APIs that will
always need a C (or Rust-with-unsafe) layer.

---

## 13. `runtime_audio_effects.c` (87 LOC) — Audio Effects

### What it does
**Stub-only** file — all functions return 0 or -1 with TODO comments:
- `rt_audio_set_pitch(sound, pitch) -> i64` — stub
- `rt_audio_add_lowpass(sound, cutoff_hz) -> i64` — stub
- `rt_audio_add_highpass(sound, cutoff_hz) -> i64` — stub
- `rt_audio_add_reverb(sound, decay, ...) -> i64` — stub
- `rt_audio_add_delay(sound, time_ms, ...) -> i64` — stub
- `rt_audio_remove_effect(sound, effect) -> i64` — stub
- `rt_audio_clear_effects(sound) -> i64` — stub

### Why must stay C (currently)
- Future implementations will call `ma_sound_set_pitch` and miniaudio DSP node APIs (C structs).
- No actual C-specific logic yet — this file is a pure stub.

### Extractable to Simple
- **Entirely extractable right now** as Simple extern stubs (since all bodies return 0). When
  real DSP is implemented, only the `ma_*` call sites need C; parameter validation and effect
  chaining logic can be Simple.

### Compiler emission potential
N/A until implemented.

---

## 14. `runtime_font.c` (231 LOC) — Font Rendering

### What it does
stb_truetype wrapper:
- `rt_font_load(path) -> handle`, `rt_font_free(handle)`
- `rt_font_glyph_bitmap(font, codepoint, size) -> bitmap_handle`
- `rt_font_glyph_bitmap_index(font, glyph_index, size) -> bitmap_handle`
- `rt_font_glyph_index(font, codepoint) -> i64`
- `rt_font_bitmap_{width,height,get_pixel,free}`
- `rt_font_glyph_advance`, `rt_font_glyph_advance_index`
- `rt_font_line_height`, `rt_font_ascent`, `rt_font_descent`, `rt_font_line_gap`

### Why must stay C
- **`#include "stb_truetype.h"`**: stb_truetype is a header-only C library compiled in one TU.
  It parses TrueType binary tables and performs rasterization in C.
- **`stbtt_BakeFontBitmap` / `stbtt_GetGlyphBitmap`**: returns `unsigned char*` bitmap pointer
  allocated by stb internally; must be freed with `stbtt_FreeBitmap`.
- **Raw font file mmap / `fread`**: reads binary TrueType data into `unsigned char[]`.

### Extractable to Simple
- The bitmap handle bookkeeping (width/height/pixel struct): pure data; could be Simple once
  the pixel buffer is exposed as `[u8]`.
- Metric calculations (`rt_font_ascent`, `rt_font_descent`, `rt_font_line_gap`): stbtt metric
  functions return `int`; the scaling math (`stbtt_ScaleForPixelHeight` * metric) is simple
  float arithmetic that Simple could do given the raw metric values.

### Compiler emission potential
Low. TrueType parsing and hinting are complex C algorithms (stb_truetype is ~5K LOC). Could be
replaced by a pure Simple TrueType parser long-term, but this is a large independent project.

---

## 15. `runtime_image.c` (90 LOC) — Image Loading

### What it does
stb_image wrapper:
- `rt_image_load(path) -> handle` — decodes PNG/JPEG/BMP/etc. into RGBA pixel buffer
- `rt_image_free(handle)`
- `rt_image_width(handle) -> i64`, `rt_image_height(handle) -> i64`
- `rt_image_channels(handle) -> i64`
- `rt_image_get_pixel(handle, x, y) -> i64` — packs RGBA into i64

### Why must stay C
- **`#define STB_IMAGE_IMPLEMENTATION` + `#include "stb_image.h"`**: stb_image compiled in this
  TU. It handles dozens of image format decoders in C.
- **`stbi_load` / `stbi_image_free`**: manages an internal C heap allocation.

### Extractable to Simple
- Pixel packing arithmetic (`get_pixel`): pure math — packs 4 `u8` into `i64`; could be Simple.
- Handle struct bookkeeping (width/height/channels/data pointer): could be a Simple struct with
  an opaque `i64` pixel-buffer token.

### Compiler emission potential
Low for decoding (same reason as font). Pixel manipulation layer (above the decoder) is
extractable.

---

## 16. `runtime_memory.c` (60 LOC) — Memory Operations

### What it does
Raw memory FFI (equivalent of `src/compiler_rust/runtime/src/value/ffi/memory.rs`):
- `rt_alloc(size) -> *u8` — `calloc(1, size)`
- `rt_free(ptr, size)` — `free(ptr)`
- `rt_ptr_read_i64(addr, offset) -> i64`, `rt_ptr_read_i32(addr, offset) -> i32`
- `rt_ptr_write_u8/i32/i64(addr, offset, value)`
- `spl_f64_to_bits(double) -> i64` — type-punning via `memcpy`
- `spl_i64_is_zero(i64) -> i32`
- `rt_memset(dst, val, n) -> *u8`, `rt_memcpy(dst, src, n) -> *u8`

### Why must stay C
- **Raw pointer arithmetic** (`(uintptr_t)addr + offset`): requires unsafe pointer casting.
- **`spl_f64_to_bits`**: uses `memcpy` for bit-level type punning — the only standard-compliant
  way in C; not expressible in Safe Simple.
- **`calloc` / `free`**: C allocator primitives; must match the mimalloc shim.
- These functions are called by the compiler-generated code for every allocation and raw pointer
  access — they are below the language abstraction floor.

### Extractable to Simple
- `spl_i64_is_zero`: trivially `value == 0`; extractable but not worth the extern round-trip.
- Nothing else: this module is at the ABI floor.

### Compiler emission potential
`rt_alloc` / `rt_free` → `@alloc` / `@free` intrinsics. `rt_ptr_read_*` / `rt_ptr_write_*`
→ `@unsafe_load` / `@unsafe_store` intrinsics. Already the right shape for compiler lowering.

---

## 17. `runtime_memtrack.c` (288 LOC) — Memory Tracking

### What it does
Debug-mode allocation tracker intercepting `SPL_MALLOC` / `SPL_CALLOC` / `SPL_REALLOC` /
`SPL_FREE`:
- `rt_memtrack_enable`, `rt_memtrack_disable`, `rt_memtrack_is_enabled`
- `rt_memtrack_alloc(size, tag) -> *void`, `rt_memtrack_realloc`, `rt_memtrack_free`
- `rt_memtrack_report` — prints live allocations with tags and (optionally) backtrace
- Uses `__builtin_return_address(0)` for caller PC capture

### Why must stay C
- **`pthread_mutex_t`** guard for the tracking hash table: required to make tracking
  thread-safe.
- **`__builtin_return_address(0)`**: GCC/Clang built-in for stack unwinding; no Simple
  equivalent.
- **Macro interception** (`#define SPL_MALLOC rt_memtrack_alloc`): compile-time macro
  substitution across all C TUs; only works in C.
- Tracking table is an intrusive linked list allocated before the allocator it tracks —
  bootstrapping constraint.

### Extractable to Simple
- Report formatting (print live allocations in tabular form): pure string/IO logic.
- Tag string management: could be Simple `HashMap<i64, text>` if the C side emits opaque tokens.

### Compiler emission potential
None. Allocation tracking is a cross-cutting concern that must intercept at the C macro level.

---

## 18. `scv_wasm_shim.c` (459 LOC) — WASM Shim

### What it does
Wraps wasmtime C embedding API + tree-sitter to run WASM grammar files for parsing:
- `wasm_rt_load(grammar_path) -> i64` — loads tree-sitter WASM grammar via wasmtime; returns
  opaque handle bundling engine/store/module/TS language pointer
- `wasm_rt_free(handle)` — releases all wasmtime resources
- `wasm_rt_parse_all(handle, source, source_len) -> text` — runs tree-sitter parse, returns
  s-expression blob

Exposes host functions to the WASM guest: `memcpy`, `memset`, `malloc`, `free` (via wasmtime
linker callback mechanism).

### Why must stay C
- **`#include <wasmtime.h>`**: wasmtime C embedding API (wasmtime_engine_t, wasmtime_module_t,
  etc.); C structs with complex lifecycle.
- **`#include <tree_sitter/api.h>`**: tree-sitter C API (TSParser, TSTree, TSNode).
- **Host function registration** (`wasmtime_linker_define_func`): requires C function pointer
  with specific ABI (`wasm_trap_t* (*)(void*, wasmtime_caller_t*, ...)`) — no Simple equivalent.
- **WASM linear memory access** (`wasmtime_memory_data`): raw `uint8_t*` pointer into the WASM
  sandbox memory; requires pointer arithmetic.

### Extractable to Simple
- Grammar path resolution and handle bookkeeping: pure logic.
- S-expression result parsing (if tree-sitter output is used to build an AST): entirely
  algorithmic; good candidate for a `std.parse.treesitter` Simple module.

### Compiler emission potential
None for the wasmtime/tree-sitter binding layer. The grammar output consumer (AST construction)
is extractable.

---

## Summary Table

| File | LOC | Core Reason Must Stay C | Extractable to Simple | Compiler Intrinsic Candidate |
|------|-----|-------------------------|----------------------|------------------------------|
| runtime.c | 2831 | `_Atomic`, `mmap`, mimalloc integration, signal-safe init | env vars, BDD hooks, debug flags | `@atomic_*`, `@mmap` |
| runtime_native.c | 1558 | Tagged-value ABI, interpreter callback, DMA, `memcpy`/`memset` bootstrap circularity | print/IO wrappers, to_string logic | `@alloc`, `@free`, `@unsafe_*` |
| runtime_thread.c | 613 | `pthread_*` opaque types, C callback ABI, Windows dual-platform | handle table, channel queue logic | None near-term |
| runtime_simd_case.c | 422 | `__attribute__((target))`, `__m128i`/`__m256i`, x86 intrinsics | scalar fallback, dispatch logic | `@Vector` / `@simd` |
| runtime_simd_dispatch.c | 52 | `__builtin_cpu_supports`, C fn-pointer dispatch tables | Nothing | `@cpu_feature` |
| runtime_simd_search.c | 599 | Same as case: SSE2/AVX2 intrinsics | Scalar fallback substring search | `@Vector` / `@simd` |
| runtime_simd_utf8.c | 631 | Same as case: SSE2/AVX2 intrinsics, dispatch init | Scalar UTF-8 loop, ASCII flag check | `@validate_utf8` |
| runtime_process.c | 273 | `fork`, `execvp`, `pipe`, `dup2`, `waitpid`, `_exit` | DAP protocol layer, argv construction | None |
| runtime_fork.c | 320 | `fork`, `pipe`, `poll`, signal reset in child | Buffer drain loop, timeout math | None |
| async_driver.c | 346 | `epoll`, `io_uring`, `kqueue`, `IOCP`, per-platform `#ifdef` | Event demux/dispatch, backend-name map | None |
| runtime_sdl2.c | 652 | SDL2 C structs, pointer-to-opaque casts, raw pixel ptr | Event enum map, SFFI wrappers | SFFI auto-gen |
| runtime_audio.c | 198 | miniaudio header-only C, OS audio APIs, realtime callback thread | Lifecycle state machine, param validation | None |
| runtime_audio_effects.c | 87 | Future `ma_*` DSP calls; **currently all stubs** | **Entire file extractable now** | N/A |
| runtime_font.c | 231 | stb_truetype header-only C, binary TrueType parsing, `stbi_FreeBitmap` | Metric math, bitmap handle bookkeeping | None near-term |
| runtime_image.c | 90 | stb_image header-only C, multi-format decoders | Pixel packing, handle bookkeeping | None |
| runtime_memory.c | 60 | Raw pointer arithmetic, `memcpy` type-pun, allocator ABI floor | `spl_i64_is_zero` (trivial) | `@alloc`, `@unsafe_load/store` |
| runtime_memtrack.c | 288 | `pthread_mutex`, `__builtin_return_address`, macro interception | Report formatting, tag management | None |
| scv_wasm_shim.c | 459 | wasmtime C API, tree-sitter C API, WASM host fn pointer ABI | Grammar path logic, AST consumer | None |

---

## Key Findings

1. **`runtime_audio_effects.c` is the only file that is immediately fully extractable** — it
   contains nothing but stubs returning 0/−1.

2. **All four SIMD files share the same root blocker**: `__attribute__((target))` + Intel
   intrinsic types. Their scalar fallback paths are all extractable today. The blocker dissolves
   once Simple gains a `@Vector` / `@simd` mechanism.

3. **`runtime_memory.c` and `runtime_native.c` (memory subset)** are at the ABI floor and
   cannot move until the compiler itself is changed — not a migration target.

4. **`async_driver.c`** is the largest architectural opportunity: the platform syscall calls
   must stay C, but the entire event-loop scheduler and task dispatcher above them can be pure
   Simple. This is the highest-leverage extraction point for the async runtime.

5. **SDL2, audio, font, image**: all are thin wrappers over external C libraries. They will
   remain C until SFFI can auto-generate bindings from C headers, or the external library is
   replaced with a pure Simple implementation.

6. **Threading**: `pthread` opaque types and C callback ABI are the hard blockers. User-space
   cooperative tasks (green threads) could eventually replace most `pthread` use at the Simple
   level, reducing this module to a minimal OS-thread pool shim.

7. **wasmtime/tree-sitter shim**: permanently C — the wasmtime embedding API is designed for
   C consumers and there is no plan to rewrite it.
