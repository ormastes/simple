# Rust Runtime Inventory — rt_* Function Migration Classification

Generated: 2026-05-17

## Summary

| Status | Count | Meaning |
|--------|-------|---------|
| C-done | ~20 | Already implemented in C (runtime_thread.c, runtime_fork.c, runtime_native.c, etc.) |
| C-ready | ~55 | Trivial wrapper — can move to C with no integration risk |
| C-possible | ~20 | Could be C but needs careful integration/UTF-8 testing |
| Simple-possible | ~15 | Could be pure Simple (higher-level logic on Simple values) |
| Rust-keep | ~100 | Must stay in Rust (complex state, crate deps, unsafe lifetime mgmt) |

---

## Tier 0 — Core (print, I/O, exit, panic, value creation)

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| print_raw | 0 | C-ready | C | Thin write(2) wrapper |
| stdin_read_char | 0 | C-ready | C | Single byte read from stdin |
| rt_stdout_write | 0 | C-ready | C | write() to fd 1 |
| rt_stdout_flush | 0 | C-ready | C | fflush(stdout) |
| rt_stderr_write | 0 | C-ready | C | write() to fd 2 |
| rt_stderr_flush | 0 | C-ready | C | fflush(stderr) |
| rt_println_value | 0 | Rust-keep | Rust | Value formatting requires Rust Display dispatch |
| rt_print_value | 0 | Rust-keep | Rust | Value formatting requires Rust Display dispatch |
| rt_eprint_value | 0 | Rust-keep | Rust | Value formatting requires Rust Display dispatch |
| rt_eprintln_value | 0 | Rust-keep | Rust | Value formatting requires Rust Display dispatch |
| rt_exit | 0 | C-ready | C | Thin exit(3) wrapper |
| rt_panic | 0 | C-ready | C | Write message + abort() |
| rt_value_int | 0 | C-possible | C | Tagged value encoding; needs ABI agreement |
| rt_value_float | 0 | C-possible | C | Tagged value encoding; needs ABI agreement |
| rt_value_bool | 0 | C-possible | C | Tagged value encoding; needs ABI agreement |
| rt_value_nil | 0 | C-possible | C | Tagged value encoding; needs ABI agreement |
| rt_to_string | 0 | Rust-keep | Rust | Value dispatch over RuntimeValue variants |
| rt_raw_u64_to_string | 0 | Rust-keep | Rust | Needs Rust integer formatting |

---

## Tier 1 — Alloc (heap-allocated structures)

### Array Operations

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_array_new | 1 | Rust-keep | Rust | Vec<RuntimeValue> allocation |
| rt_byte_array_new | 1 | Rust-keep | Rust | Vec<u8> allocation |
| rt_array_push | 1 | Rust-keep | Rust | Vec push; RuntimeValue ownership |
| rt_array_get | 1 | Rust-keep | Rust | Index into Vec<RuntimeValue> |
| rt_array_get_text | 1 | Rust-keep | Rust | Index + text conversion |
| rt_array_data_ptr_text | 1 | Rust-keep | Rust | Raw pointer into Vec; unsafe lifetime |
| rt_array_data_ptr_u8 | 1 | Rust-keep | Rust | Raw pointer into Vec<u8>; unsafe |
| rt_array_set | 1 | Rust-keep | Rust | Indexed assignment into Vec<RuntimeValue> |
| rt_array_set_text | 1 | Rust-keep | Rust | Indexed assignment + text |
| rt_array_set_len_known_text | 1 | Rust-keep | Rust | Pre-sized buffer set |
| rt_bytes_u8_at | 1 | Rust-keep | Rust | Byte access into RuntimeValue buffer |
| rt_bytes_u32_le_at | 1 | Rust-keep | Rust | LE u32 read |
| rt_bytes_u64_le_at | 1 | Rust-keep | Rust | LE u64 read |
| rt_typed_bytes_u8_push | 1 | Rust-keep | Rust | Typed push |
| rt_typed_words_u32_at | 1 | Rust-keep | Rust | Typed word read |
| rt_typed_words_u32_push | 1 | Rust-keep | Rust | Typed word push |
| rt_typed_words_u32_set | 1 | Rust-keep | Rust | Typed word set |
| rt_array_pop | 1 | Rust-keep | Rust | Vec pop |
| rt_array_first | 1 | Rust-keep | Rust | First element access |
| rt_array_clear | 1 | Rust-keep | Rust | Vec::clear |
| rt_array_len | 1 | Rust-keep | Rust | Vec::len |
| rt_range | 1 | Rust-keep | Rust | Range iterator construction |
| rt_range_inclusive | 1 | Rust-keep | Rust | Inclusive range |

### Tuple

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_tuple_new | 1 | Rust-keep | Rust | Vec<RuntimeValue> tuple |
| rt_tuple_set | 1 | Rust-keep | Rust | Positional set |
| rt_tuple_get | 1 | Rust-keep | Rust | Positional get |
| rt_tuple_len | 1 | Rust-keep | Rust | Vec::len |

### Dict

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_dict_new | 1 | Rust-keep | Rust | HashMap<String,RuntimeValue> |
| rt_dict_set | 1 | Rust-keep | Rust | HashMap insert |
| rt_dict_get | 1 | Rust-keep | Rust | HashMap lookup |
| rt_dict_len | 1 | Rust-keep | Rust | HashMap::len |
| rt_dict_clear | 1 | Rust-keep | Rust | HashMap::clear |
| rt_dict_keys | 1 | Rust-keep | Rust | Collect key vec |
| rt_dict_values | 1 | Rust-keep | Rust | Collect value vec |

### Index / Slice

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_index_get | 1 | Rust-keep | Rust | Dispatches over array/dict/string |
| rt_index_set | 1 | Rust-keep | Rust | Dispatches over mutable containers |
| rt_slice | 1 | Rust-keep | Rust | Slice of array/string |
| rt_contains | 1 | Rust-keep | Rust | Polymorphic contains check |

### String Operations

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_string_new | 1 | C-possible | C | UTF-8 alloc; needs careful null-term policy |
| rt_string_concat | 1 | C-possible | C | Alloc + memcpy; UTF-8 safe |
| rt_string_len | 1 | C-possible | C | byte length (not codepoints) |
| rt_string_data | 1 | C-possible | C | Raw pointer to bytes |
| rt_cstring_to_text | 1 | C-possible | C | CStr → RuntimeValue text |
| rt_string_char_at | 1 | C-possible | C | UTF-8 char_at; moderate complexity |
| rt_string_split | 1 | Simple-possible | Simple | Higher-level; build on C string primitives |
| rt_string_replace | 1 | Simple-possible | Simple | Higher-level |
| rt_string_trim | 1 | Simple-possible | Simple | Higher-level |
| rt_string_join | 1 | Simple-possible | Simple | Higher-level |
| rt_string_to_upper | 1 | Simple-possible | Simple | Unicode-aware; once primitives exist |
| rt_string_to_lower | 1 | Simple-possible | Simple | Unicode-aware |
| rt_string_to_int | 1 | Simple-possible | Simple | Parse loop |
| rt_string_find | 1 | Simple-possible | Simple | Search loop |
| rt_string_rfind | 1 | Simple-possible | Simple | Reverse search |
| rt_string_index_of | 1 | Simple-possible | Simple | Higher-level find |
| rt_string_eq | 1 | Simple-possible | Simple | memcmp wrapper |
| rt_string_starts_with | 1 | Simple-possible | Simple | Prefix check |
| rt_string_ends_with | 1 | Simple-possible | Simple | Suffix check |

### UTF-8

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_utf8_count_codepoints | 1 | C-ready | C | Byte-level scan |
| rt_utf8_validate | 1 | C-ready | C | Byte-level validation |
| rt_utf8_find_invalid | 1 | C-ready | C | Returns first invalid byte offset |
| rt_text_count_codepoints | 1 | C-ready | C | Alias/wrapper of above |

### SWI / Rank-Select (bit-parallel succinct data structures)

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_swi_build | 1 | Rust-keep | Rust | Bit-parallel wavelet index; Rust unsafe |
| rt_swi_char_to_byte | 1 | Rust-keep | Rust | Wavelet query |
| rt_swi_byte_to_char | 1 | Rust-keep | Rust | Wavelet query |
| rt_swi_free | 1 | Rust-keep | Rust | Drop wavelet index |
| rt_rank_select_build | 1 | Rust-keep | Rust | Succinct bitvector |
| rt_rank_query | 1 | Rust-keep | Rust | Popcount prefix query |
| rt_select_query | 1 | Rust-keep | Rust | nth-set-bit query |
| rt_rank_select_free | 1 | Rust-keep | Rust | Drop bitvector |

### Hash

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_hash_text | 1 | C-ready | C | FNV/xxHash; byte-level |

### Object

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_object_new | 1 | Rust-keep | Rust | HashMap + vtable; complex |
| rt_object_field_get | 1 | Rust-keep | Rust | HashMap lookup |
| rt_object_field_set | 1 | Rust-keep | Rust | HashMap insert |

### Closure

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_closure_new | 1 | Rust-keep | Rust | Captures + fn ptr |
| rt_closure_set_capture | 1 | Rust-keep | Rust | Capture slot write |
| rt_closure_get_capture | 1 | Rust-keep | Rust | Capture slot read |
| rt_closure_func_ptr | 1 | Rust-keep | Rust | Raw fn pointer extraction |

### Enum

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_enum_check_discriminant | 1 | Rust-keep | Rust | Tag comparison |
| rt_enum_new | 1 | Rust-keep | Rust | Tagged value construction |
| rt_enum_discriminant | 1 | Rust-keep | Rust | Tag extraction |
| rt_enum_payload | 1 | Rust-keep | Rust | Payload extraction |

### Memory / Raw Pointer

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_alloc | 1 | C-ready | C | malloc wrapper |
| rt_free | 1 | C-ready | C | free wrapper |
| rt_ptr_to_value | 1 | C-ready | C | usize → RuntimeValue |
| rt_value_to_ptr | 1 | C-ready | C | RuntimeValue → usize |
| rt_memset | 1 | C-ready | C | memset wrapper |
| rt_memcpy | 1 | C-ready | C | memcpy wrapper |
| rt_ptr_read_i64 | 1 | C-ready | C | Dereference raw pointer |
| rt_ptr_write_u8 | 1 | C-ready | C | Raw pointer write |
| rt_ptr_write_i32 | 1 | C-ready | C | Raw pointer write |
| rt_ptr_write_i64 | 1 | C-ready | C | Raw pointer write |

### Hashmap / Btreemap / Sets

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_hashmap_* | 1 | Rust-keep | Rust | HashMap<K,V> over RuntimeValue |
| rt_btreemap_* | 1 | Rust-keep | Rust | BTreeMap; ordered traversal |
| rt_hashset_* | 1 | Rust-keep | Rust | HashSet over RuntimeValue |
| rt_btreeset_* | 1 | Rust-keep | Rust | BTreeSet; ordered |

### Unique / Shared / Weak / Handle refs

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_unique_* | 1 | Rust-keep | Rust | Box<T> ownership |
| rt_shared_* | 1 | Rust-keep | Rust | Arc<T> ref-counting |
| rt_weak_* | 1 | Rust-keep | Rust | Weak<T> weak refs |
| rt_handle_* | 1 | Rust-keep | Rust | Opaque handle registry |

---

## Tier 2 — Sys (OS-dependent)

### Time

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_time_now_unix | 2 | C-ready | C | clock_gettime(CLOCK_REALTIME) |
| rt_time_now_nanos | 2 | C-ready | C | CLOCK_MONOTONIC ns |
| rt_time_now_micros | 2 | C-ready | C | CLOCK_MONOTONIC µs |
| rt_time_now_unix_micros | 2 | C-ready | C | CLOCK_REALTIME µs |
| rt_sleep_ms | 2 | C-ready | C | nanosleep wrapper |

### Env / Process

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_env_get | 2 | C-ready | C | getenv wrapper |
| rt_set_env | 2 | C-ready | C | setenv wrapper |
| rt_get_args | 2 | C-ready | C | argv array |
| rt_platform_name | 2 | C-ready | C | Compile-time string |
| rt_process_* | 2 | C-done | C | Implemented in runtime_process.c |
| rt_exec* | 2 | C-done | C | Implemented in runtime_process.c |

### File I/O

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_file_read_text | 2 | C-possible | C | Needs UTF-8 validation on read |
| rt_file_write_text | 2 | C-possible | C | Needs encoding handling |
| rt_write_file | 2 | C-possible | C | Binary write path is simpler |

### Regex

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| ffi_regex_is_match | 2 | Rust-keep | Rust | regex crate; NFA engine |
| ffi_regex_find | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_find_all | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_captures | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_replace | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_replace_all | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_split | 2 | Rust-keep | Rust | regex crate |
| ffi_regex_split_n | 2 | Rust-keep | Rust | regex crate |

### Coverage / Sandbox

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_coverage_* | 2 | Rust-keep | Rust | Coverage instrumentation state |
| rt_sandbox_* | 2 | Rust-keep | Rust | Sandbox enforcement logic |

---

## Tier 3 — Async (concurrency)

### Threads

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_thread_spawn_isolated | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_spawn_isolated2 | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_join | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_is_done | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_id | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_free | 3 | C-done | C | Implemented in runtime_thread.c |
| rt_thread_available_parallelism | 3 | C-done | C | Implemented in runtime_thread.c |

### Futures / Actors

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_wait | 3 | Rust-keep | Rust | Async executor integration |
| rt_future_new | 3 | Rust-keep | Rust | Future construction; Rust async runtime |
| rt_future_await | 3 | Rust-keep | Rust | Poll loop; Rust async runtime |
| rt_actor_* | 3 | Rust-keep | Rust | Actor mailbox + executor |
| rt_channel_* | 3 | Rust-keep | Rust | MPSC channel over RuntimeValue |
| rt_executor_* | 3 | Rust-keep | Rust | Task scheduler |
| rt_generator_* | 3 | Rust-keep | Rust | Generator coroutine state |

---

## Tier 4 — Ext (hardware extensions)

### Math (28 functions)

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_math_pow | 4 | C-ready | C | pow() from libm |
| rt_math_log | 4 | C-ready | C | log() from libm |
| rt_math_log10 | 4 | C-ready | C | log10() from libm |
| rt_math_log2 | 4 | C-ready | C | log2() from libm |
| rt_math_exp | 4 | C-ready | C | exp() from libm |
| rt_math_sqrt | 4 | C-ready | C | sqrt() from libm |
| rt_math_cbrt | 4 | C-ready | C | cbrt() from libm |
| rt_math_sin | 4 | C-ready | C | sin() from libm |
| rt_math_cos | 4 | C-ready | C | cos() from libm |
| rt_math_tan | 4 | C-ready | C | tan() from libm |
| rt_math_asin | 4 | C-ready | C | asin() from libm |
| rt_math_acos | 4 | C-ready | C | acos() from libm |
| rt_math_atan | 4 | C-ready | C | atan() from libm |
| rt_math_atan2 | 4 | C-ready | C | atan2() from libm |
| rt_math_sinh | 4 | C-ready | C | sinh() from libm |
| rt_math_cosh | 4 | C-ready | C | cosh() from libm |
| rt_math_tanh | 4 | C-ready | C | tanh() from libm |
| rt_math_floor | 4 | C-ready | C | floor() from libm |
| rt_math_ceil | 4 | C-ready | C | ceil() from libm |
| rt_math_round | 4 | C-ready | C | round() from libm |
| rt_math_trunc | 4 | C-ready | C | trunc() from libm |
| rt_math_abs | 4 | C-ready | C | fabs() / abs() |
| rt_math_hypot | 4 | C-ready | C | hypot() from libm |
| rt_math_gcd | 4 | C-ready | C | Integer loop; no libm needed |
| rt_math_min | 4 | C-ready | C | fmin() / integer compare |
| rt_math_max | 4 | C-ready | C | fmax() / integer compare |
| rt_math_clamp | 4 | C-ready | C | min/max composition |
| rt_math_fma | 4 | C-ready | C | fma() from libm |

### SIMD

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_simd_* | 4 | Rust-keep | Rust | Rust SIMD intrinsics; portable_simd |
| rt_vec_* | 4 | Rust-keep | Rust | SIMD vector ops |

### GPU / CUDA / Vulkan

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_gpu_* | 4 | Rust-keep | Rust | GPU state machine; complex lifecycle |
| rt_cuda_* | 4 | Rust-keep | Rust | CUDA driver API; dlopen + unsafe |
| rt_vk_* | 4 | Rust-keep | Rust | Vulkan state; ash crate |

### Numeric Extensions

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_numeric_* | 4 | Rust-keep | Rust | Extended numeric types |

### Cranelift JIT

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_cranelift_* | 4 | Rust-keep | Rust | JIT module management; cranelift crate |

---

## AOP

| Function | Tier | Status | Target | Notes |
|----------|------|--------|--------|-------|
| rt_aop_invoke_around | — | Rust-keep | Rust | Complex dispatch over advice chain |
| rt_aop_proceed | — | Rust-keep | Rust | Continue advice chain |

---

## Migration Priority Order

1. **C-ready (Math, 28 fns)** — pure libm delegates; zero runtime coupling; highest ROI
2. **C-ready (Memory/Ptr, ~10 fns)** — malloc/free/memcpy; straightforward
3. **C-ready (I/O, ~6 fns)** — write()/fflush(); already thin in Rust
4. **C-ready (UTF-8, 4 fns)** — byte-level; no allocator coupling
5. **C-ready (Time, 5 fns)** — clock_gettime wrappers
6. **C-ready (Env, 4 fns)** — getenv/setenv/argv
7. **C-possible (String core, 6 fns)** — needs ABI + encoding test plan
8. **C-possible (Value creation, 4 fns)** — requires tagged-value ABI agreement
9. **C-possible (File I/O, ~3 fns)** — UTF-8 path handling required
10. **Simple-possible (String high-level, ~13 fns)** — after C core is in place
