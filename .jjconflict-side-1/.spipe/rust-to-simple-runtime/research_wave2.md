# Wave-2 Runtime Conversion Research: Medium C Modules

**Date:** 2026-05-18
**Scope:** `src/runtime/` — 6 medium-complexity C files (292+261+113+175+152+48 = 1041 LOC)
**Goal:** Assess each for pure-Simple conversion feasibility

---

## 1. `runtime_format.c` (292 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `__c_rt_value_format_string` | `(RuntimeValue v, const uint8_t *fmt_ptr, uint64_t fmt_len, uint8_t *out, uint64_t out_cap) -> i64` | Format a runtime value using a Python-style format spec (`{:>10.2f}`, `{:#x}`, etc.) into a caller-provided output buffer. Returns bytes written. |
| `__c_rt_value_to_display_str` | `(RuntimeValue v, uint8_t *out, uint64_t out_cap) -> i64` | Convert any runtime value to its display representation (no format spec). |

**Internal helpers (static, not exported):**
- `parse_format_spec()` — parses fill/align/sign/alt/width/precision/type from a format string
- `format_sign()` — prepends sign character to raw numeral
- `format_pad()` — pads to width with fill char + alignment

### Format spec capabilities
Supports type codes: `f`, `F`, `e`, `E`, `d`, `x`, `X`, `o`, `b`, `%`, `s`. Handles fill-align (`<`, `>`, `^`), sign (`+`, ` `), alt-form (`#`), zero-fill, width, and precision.

### Existing Simple Equivalent
None found in `src/lib/`. The file `src/lib/nogc_sync_mut/cli/formatting.spl` exists but is CLI-level (wraps `rt_format_*` if any). The two `__c_rt_*` symbols are called directly from the Rust runtime:
- `src/compiler_rust/runtime/src/value/ffi/io_print.rs` — links them via `#[link_name]`.

### Dependencies
- `<stdlib.h>`, `<string.h>` — `snprintf`, `fabs`, `memcpy`
- `runtime_value.h` — `RuntimeValue`, `rv_is_int()`, `rv_is_float()`, `rv_is_str()`, `rv_to_int()`, `rv_to_float()`, `rt_string_new()`
- No other C runtime modules

### Conversion Difficulty: **HIGH**
- The function uses raw output buffers (`uint8_t *out, uint64_t out_cap`) that map to C ABI pointer passing — not directly expressible in Simple without `[u8]` buffer SFFI.
- `snprintf` is used for the `f`/`e`/`E` type codes — would need a Simple-native float formatting routine or an SFFI extern to `snprintf`.
- Format spec parsing is pure algorithmic logic (easy in Simple), but float-to-string conversion is the hard part.
- Wired to Rust runtime via `#[link_name]` — changing the C implementation requires no compiler changes, but replacing it with a pure-Simple function requires a new ABI bridge.

### Performance Notes
- Hot path: every string interpolation calls `__c_rt_value_to_display_str`. Must be fast.
- The `snprintf` calls for float formatting are the bottleneck; a pure-Simple float formatter would be slower unless the compiler can optimize it well.

### SFFI Externs Needed (if converted)
```
extern fn rt_snprintf_f64(value: f64, precision: i32, out: [u8]) -> i64  // or keep snprintf bridge
extern fn rt_fabs(x: f64) -> f64
```

---

## 2. `runtime_string_index.c` (261 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `rt_swi_build` | `(i64 value) -> i64` | Build a Segmented Width Index (SWI) for a string value. Returns opaque handle (heap pointer). O(n) build. |
| `rt_swi_char_to_byte` | `(i64 handle, i64 char_idx) -> i64` | Convert char index → byte offset. O(log S + W). |
| `rt_swi_byte_to_char` | `(i64 handle, i64 byte_idx) -> i64` | Convert byte offset → char index. O(log S + W). |
| `rt_swi_free` | `(i64 handle)` | Free SWI heap allocation. |
| `rt_rank_select_build` | `(i64 value) -> i64` | Build a Rank/Select bitvector index over a string. Returns opaque handle. |
| `rt_rank_query` | `(i64 handle, i64 pos) -> i64` | Count 1-bits in positions [0..pos). O(1) via popcount + block table. |
| `rt_select_query` | `(i64 handle, i64 k) -> i64` | Find position of k-th 1-bit. O(log n) binary search. |
| `rt_rank_select_free` | `(i64 handle)` | Free rank/select heap allocation. |

### Existing Simple Equivalent
None found. No `src/lib/` code calls `rt_swi_*` or `rt_rank_*`. These are specialist data-structure functions; callers not found in `src/compiler/` SPL either.

### Dependencies
- `runtime_simd_dispatch.h` — for `simd_as_string()`, `RtCoreStringSimd` struct
- `<stdlib.h>` — `malloc`, `free`
- `__builtin_popcountll` (GCC/Clang builtin)

### Conversion Difficulty: **VERY HIGH**
- Handles are raw heap pointers cast to `i64` — classic C pointer-passing pattern. Simple has no equivalent without unsafe memory management.
- Depends on `simd_as_string()` from the SIMD dispatch layer — would need a corresponding Simple SFFI extern.
- `__builtin_popcountll` needs an SFFI extern or a Simple bit-count implementation.
- Since no compiler or lib code currently calls these, conversion priority is low.

### Performance Notes
- SWI and rank/select are explicitly performance structures (the file's own comment says O(log S + W) and O(1) rank).
- Must remain in native code or be extremely carefully optimized in Simple. Hot if UTF-8 indexing is on the critical path.

### SFFI Externs Needed
```
extern fn rt_simd_string_data(value: i64) -> i64   // raw pointer to string bytes
extern fn rt_simd_string_len(value: i64) -> i64
extern fn rt_popcnt64(x: i64) -> i64
extern fn rt_malloc(size: i64) -> i64
extern fn rt_free(ptr: i64)
```

---

## 3. `runtime_random.c` (113 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `rt_random_seed` | `(i64 seed)` | Set LCG seed (thread-safe, mutex-guarded). |
| `rt_random_getstate` | `() -> i64` | Get current RNG state. |
| `rt_random_setstate` | `(i64 new_state)` | Set RNG state (for reproducibility). |
| `rt_random_next` | `() -> i64` | Advance LCG, return raw state. |
| `rt_random_randint` | `(i64 min, i64 max) -> i64` | Random int in [min, max] via modulo. |
| `rt_random_random` | `() -> f64` | Random float in [0.0, 1.0). |
| `rt_random_uniform` | `(f64 min, f64 max) -> f64` | Random float in [min, max). |
| `__c_rt_random_hex_buf` | `(uint8_t *out, i64 byte_count) -> i64` | Fill output buffer with random hex bytes. |

**Algorithm:** LCG with A=1664525, C=1013904223, M=2^32 (Numerical Recipes constants). Global state protected by `pthread_mutex_t`.

### Existing Simple Equivalent
**Partial.** `src/lib/nogc_sync_mut/src/core/random.spl` exists and already wraps all the `rt_random_*` externs as Simple functions (`seed`, `getstate`, `setstate`, `next`, `randint`, `random`, `uniform`). The Simple layer is thin — it's just FFI wrappers with high-level operations (shuffle, choice, sample, gaussian, exponential) built in pure Simple on top.

### Dependencies
- `<pthread.h>` — `pthread_mutex_t`, `pthread_mutex_lock/unlock`
- `<time.h>` — `clock_gettime(CLOCK_REALTIME)` for auto-seeding
- `<stdlib.h>` — no `rand()` used (implements its own LCG)

### Conversion Difficulty: **MEDIUM-LOW**
- The LCG arithmetic is trivially portable to Simple (multiplication + modulo on i64).
- The mutex is the main obstacle — Simple would need an `extern fn rt_mutex_lock/unlock` SFFI or rely on the runtime's existing sync primitives.
- Auto-seed via `clock_gettime` → `rt_time_now_unix_micros()` already exists as an extern.
- `__c_rt_random_hex_buf` uses a raw output buffer — would need buffer SFFI.

### SFFI Externs Needed (if converted)
```
extern fn rt_time_now_unix_micros() -> i64   // already exists
extern fn rt_mutex_create() -> i64
extern fn rt_mutex_lock(handle: i64)
extern fn rt_mutex_unlock(handle: i64)
// OR: use atomic i64 via existing rt_atomic externs if available
```

### Performance Notes
- Mutex lock/unlock on every call is the bottleneck. Not a hot inner loop in typical usage.

---

## 4. `runtime_time.c` (175 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `rt_time_now_unix_micros` | `() -> i64` | Wall clock micros since Unix epoch (CLOCK_REALTIME). |
| `rt_time_now_nanos` | `() -> i64` | Monotonic nanos from process-local epoch (CLOCK_MONOTONIC). |
| `rt_time_now_micros` | `() -> i64` | Monotonic micros (= nanos / 1000). |
| `rt_time_now_seconds_f64` | `() -> f64` | Wall clock seconds as fractional f64. |
| `rt_timestamp_get_year` | `(i64 micros) -> i32` | Extract year from Unix-epoch micros (Howard Hinnant algorithm). |
| `rt_timestamp_get_month` | `(i64 micros) -> i32` | Extract month (1–12). |
| `rt_timestamp_get_day` | `(i64 micros) -> i32` | Extract day (1–31). |
| `rt_timestamp_get_hour` | `(i64 micros) -> i32` | Extract hour (0–23). |
| `rt_timestamp_get_minute` | `(i64 micros) -> i32` | Extract minute (0–59). |
| `rt_timestamp_get_second` | `(i64 micros) -> i32` | Extract second (0–59). |
| `rt_timestamp_get_microsecond` | `(i64 micros) -> i32` | Extract microsecond component. |
| `rt_timestamp_from_components` | `(i32 year, i32 month, i32 day, i32 h, i32 m, i32 s, i32 us) -> i64` | Compose Unix-epoch micros from civil date+time. |
| `rt_timestamp_add_days` | `(i64 micros, i64 days) -> i64` | Add N days (in microseconds). |
| `rt_timestamp_diff_days` | `(i64 micros1, i64 micros2) -> i64` | Difference in days. |
| `rt_progress_init` | `()` | Initialize monotonic progress timer (process-local). |
| `rt_progress_reset` | `()` | Reset progress timer start point. |
| `rt_progress_get_elapsed_seconds` | `() -> f64` | Seconds since progress timer init. |

### Existing Simple Equivalent
**Partial.** `src/lib/nogc_sync_mut/src/time.spl` and `src/lib/nogc_sync_mut/io/time_ops.spl` wrap only `rt_time_now_unix_micros()`. The civil-date functions (`rt_timestamp_get_year` etc.) are NOT yet wrapped. The Simple `time.spl` implements `timestamp_year` as a crude approximation (`1970 + seconds / (365*24*3600)`) — not using the C Howard Hinnant algorithm.

### Dependencies
- `<time.h>` — `clock_gettime`, `struct timespec`, `CLOCK_REALTIME`, `CLOCK_MONOTONIC`
- Static process-local state for monotonic origin and progress timer

### Conversion Difficulty: **MEDIUM**
- Clock calls (`clock_gettime`) need SFFI or to remain as thin C stubs.
- Civil date arithmetic (Howard Hinnant days-to-date) is pure arithmetic — fully portable to Simple once `clock_gettime` is an extern.
- Progress timer uses static initialized state — Simple module-level `var` could hold this.
- The comment says "C equivalents of `src/compiler_rust/runtime/src/value/ffi/time.rs`" — the Rust version exists, so the logic is well-understood.

### SFFI Externs Needed (if converted)
```
extern fn rt_clock_realtime_micros() -> i64    // thin C: clock_gettime(REALTIME)
extern fn rt_clock_monotonic_nanos() -> i64    // thin C: clock_gettime(MONOTONIC)
```
The civil-date functions and progress timer become pure Simple on top.

### Performance Notes
- Clock calls are syscalls — no additional overhead introduced by Simple wrappers.
- Civil date decomposition is called infrequently (formatting timestamps).

---

## 5. `runtime_env.c` (152 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `__c_rt_env_get_i64` | `(uint8_t *name, u64 len, i64 default) -> i64` | Get env var, parse as integer. |
| `__c_rt_env_set` | `(uint8_t *name, u64 nlen, uint8_t *val, u64 vlen) -> bool` | Set env var via `setenv`. |
| `__c_rt_set_env` | `(uint8_t *name, u64 nlen, uint8_t *val, u64 vlen)` | Alias for `__c_rt_env_set` (void return). |
| `__c_rt_env_exists` | `(uint8_t *name, u64 len) -> bool` | Test env var presence via `getenv`. |
| `__c_rt_env_remove` | `(uint8_t *name, u64 len) -> bool` | Remove env var via `unsetenv`. |
| `__c_rt_exit` | `(i32 code)` | Call `exit(code)`. |
| `__c_rt_stdout_flush` | `() -> i64` | `fflush(stdout)`. |
| `__c_rt_stderr_flush` | `() -> i64` | `fflush(stderr)`. |
| `__c_rt_platform_name` | `(uint8_t **out_ptr) -> i64` | Return static string `"linux"`, `"macos"`, `"windows"`, or `"freebsd"`. |
| `__c_rt_env_cwd` | `(uint8_t *out, u64 cap) -> i64` | `getcwd` into buffer. |
| `__c_rt_env_temp` | `(uint8_t *out, u64 cap) -> i64` | Write temp dir path (`/tmp` or `%TEMP%`). |
| `__c_rt_term_get_size` | `(i32 *cols, i32 *rows)` | Get terminal dimensions via `ioctl(TIOCGWINSZ)`. |

### Existing Simple Equivalent
**Significant overlap.** The Simple layer is split across multiple files:
- `src/lib/nogc_sync_mut/io/env_ops.spl` — wraps `rt_env_get(key: text) -> text`, `rt_env_set`, `rt_env_vars`, `rt_env_cwd` (note: different ABI — text not ptr+len)
- `src/lib/nogc_sync_mut/shell/env.spl` — `get(key) -> text`, `set(key, value) -> bool`, `cwd() -> text`
- `src/compiler/20.hir/hir_lowering/expressions.spl` — directly uses `extern fn rt_env_get(key: text) -> text`

**Key ABI mismatch:** The C file uses `(uint8_t *ptr, uint64_t len)` ABI for name/value, but the Simple externs use `(key: text)` — indicating the Rust runtime has a second layer that does the text-to-ptr conversion. The C module serves the Rust runtime's raw call path.

### Dependencies
- `<stdlib.h>` — `getenv`, `setenv`, `unsetenv`, `malloc`, `free`
- `<unistd.h>` — `getcwd`
- `<stdio.h>` — `fflush`, `stdout`, `stderr`
- `<sys/ioctl.h>` — `TIOCGWINSZ` (terminal size)
- Platform `#ifdef` for macOS/Linux/Windows/FreeBSD

### Conversion Difficulty: **HIGH** (for full ABI parity) / **MEDIUM** (for Simple-facing API)
- The `(ptr, len)` ABI functions cannot be expressed in Simple without buffer SFFI.
- However the Simple-level API (`rt_env_get(key: text)`) is already wrapped — the C layer is only needed for the Rust runtime's raw path.
- `__c_rt_exit`, `__c_rt_stdout_flush`, `__c_rt_stderr_flush` must remain thin C stubs (no Simple equivalent for `exit()` or `fflush()`).
- `__c_rt_platform_name` is trivial but needs compile-time `#ifdef` — hard in Simple without SFFI.
- `__c_rt_term_get_size` requires `ioctl` — must stay C or be a thin SFFI extern.

### SFFI Externs Needed (if partially converted)
```
extern fn rt_syscall_exit(code: i32)
extern fn rt_syscall_stdout_flush() -> i64
extern fn rt_syscall_stderr_flush() -> i64
extern fn rt_syscall_getcwd(out: [u8]) -> i64
extern fn rt_syscall_term_size(cols: &mut i32, rows: &mut i32)
```

---

## 6. `runtime_regex_stub.c` (48 LOC)

### Exported Functions

| Symbol | Signature | Purpose |
|--------|-----------|---------|
| `ffi_regex_is_match` | `(RuntimeValue pattern, RuntimeValue text) -> RuntimeValue` | Stub — always returns `RT_FALSE`. |
| `ffi_regex_find` | `(RuntimeValue pattern, RuntimeValue text) -> RuntimeValue` | Stub — returns empty array. |
| `ffi_regex_find_all` | `(RuntimeValue pattern, RuntimeValue text) -> RuntimeValue` | Stub — returns empty array. |
| `ffi_regex_captures` | `(RuntimeValue pattern, RuntimeValue text) -> RuntimeValue` | Stub — returns empty array. |
| `ffi_regex_replace` | `(RuntimeValue pattern, RuntimeValue text, RuntimeValue replacement) -> RuntimeValue` | Stub — returns input text unchanged. |
| `ffi_regex_replace_all` | `(…) -> RuntimeValue` | Stub — returns input text unchanged. |
| `ffi_regex_split` | `(RuntimeValue pattern, RuntimeValue text) -> RuntimeValue` | Stub — returns array with input text as single element. |
| `ffi_regex_split_n` | `(…, RuntimeValue limit) -> RuntimeValue` | Stub — returns array with input text as single element. |

### Existing Simple Equivalent
**Yes — and the real implementation exists in Rust.** The file `src/compiler_rust/runtime/src/value/ffi/regex.rs` provides the real `ffi_regex_*` implementations using the `regex` Rust crate. The C stub is a fallback for builds without the Rust runtime.

The Simple library has:
- `src/lib/nogc_sync_mut/io/regex_ffi.spl` — full Simple wrapper around `rt_regex_new/destroy/is_match/find/find_all/captures/replace/replace_all/split` (handle-based API, different from the stub's pattern-per-call API)
- `src/lib/nogc_sync_mut/src/core/regex.spl`, `src/lib/nogc_sync_mut/src/tooling/regex_nfa.spl` — pure-Simple NFA regex engine

### Dependencies
- `runtime_value.h` — `RuntimeValue`, `RT_FALSE`, `rt_array_new`, `rt_array_push`
- The C stub uses `rt_array_new` and `rt_array_push` (other C runtime functions)
- The real implementation: Rust `regex` crate

### Conversion Difficulty: **TRIVIAL** (stub) / **N/A** (real impl already in Rust)
- The C stub file itself is already nearly a no-op. It exists only so the C build can link without the Rust regex crate.
- A Simple stub equivalent would just return `false` and empty arrays — same as now.
- The pure-Simple NFA engine (`regex_nfa.spl`) could replace the stub in interpreter mode.
- **Recommended action:** Do not convert the stub. Instead, wire `regex_nfa.spl` as the interpreter-mode fallback.

---

## Summary Table

| File | LOC | Exports | Simple Wrapper Exists | Conversion Difficulty | Priority |
|------|-----|---------|----------------------|----------------------|----------|
| `runtime_format.c` | 292 | 2 | None | HIGH (float formatting, raw buffers) | LOW |
| `runtime_string_index.c` | 261 | 8 | None | VERY HIGH (SIMD deps, heap handles) | SKIP (unused) |
| `runtime_random.c` | 113 | 8 | Yes (random.spl) | MEDIUM-LOW (LCG pure logic, mutex SFFI) | MEDIUM |
| `runtime_time.c` | 175 | 17 | Partial (time.spl) | MEDIUM (2 clock SFFIs + pure arithmetic) | HIGH |
| `runtime_env.c` | 152 | 12 | Partial (env_ops.spl) | HIGH (ptr ABI, ioctl, platform ifdefs) | LOW |
| `runtime_regex_stub.c` | 48 | 8 | Yes (regex_ffi.spl + NFA) | TRIVIAL / N/A | SKIP |

---

## Recommended Conversion Order

1. **`runtime_time.c` (HIGH priority):** Civil-date arithmetic and progress timer are pure math. Add two thin SFFI externs (`rt_clock_realtime_micros`, `rt_clock_monotonic_nanos`) and port the 15 functions to Simple. Fix the wrong `timestamp_year` approximation in `time.spl` as part of the port.

2. **`runtime_random.c` (MEDIUM priority):** LCG is trivial arithmetic. Main risk is mutex — evaluate using `rt_atomic_cas` if available instead of full mutex. Port `rt_random_seed/next/randint/random/uniform`; keep `__c_rt_random_hex_buf` as C (raw buffer dependency).

3. **`runtime_env.c` (LOW priority):** The Simple-facing API is already wrapped. The C file's real value is the `(ptr, len)` ABI bridge for the Rust runtime and the `ioctl`/`getcwd`/`exit`/`fflush` calls that must stay native. Defer.

4. **`runtime_format.c` (LOW priority):** Float-to-string is the blocker. Defer until Simple has a native float formatter or a safe `snprintf` SFFI.

5. **`runtime_string_index.c` (SKIP):** No callers in the Simple compiler. The SIMD dependency and heap-handle pattern make this extremely hard to port. Leave in C.

6. **`runtime_regex_stub.c` (SKIP):** Stub with no real logic. The real implementation is in Rust. Wire `regex_nfa.spl` for interpreter-mode use instead of porting the stub.
