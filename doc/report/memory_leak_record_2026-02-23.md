# Memory Leak Record — C Codegen Runtime

Date: 2026-02-23
Status: All 9 leak categories fixed. Zero ASan leaks across 42 code paths.

## Leak Commit Timeline

| Commit | File | Leaks | Status |
|--------|------|-------|--------|
| `vxz` | main.c (1202L) | Non-compilable (pseudo-Simple syntax) | N/A |
| `u`, `tzv` | main.c (1202L) | Same non-compilable | N/A |
| `wul`-`usqq` | main.c (220L) | No allocations | CLEAN |
| `wr` (◆) | main.c (617L) | Leaks 5-9: 25 allocs, 0 frees | LEAKS (immutable) |
| `psl` (◆ main) | main.c (617L) + c_runtime.c | Leaks 1-9: all categories | LEAKS (immutable) |
| **`qn` (○ fix)** | main.c + c_runtime.c + bootstrap | **All 9 fixed** | **CLEAN** |
| `o`-`lm` (○) | inherited from qn | All fixes inherited | CLEAN |

## Leak Categories

### Leak 1: Nested array free functions missing
- **Introduced:** c_runtime.c has always been missing these
- **Cause:** `[[text]]`/`[[i64]]` types had no free functions
- **Fix:** Added `simple_string_array_array_free()` and `simple_int_array_array_free()`
- **File:** `src/app/compile/c_runtime.c`
- **First fixed:** `qn`

### Leak 2: String copy_push shallow-copied
- **Cause:** `simple_string_array_copy_push()` did `dst.items[i] = src.items[i]` (shallow)
- **Fix:** Deep-copy via `strdup(src.items[i] ? src.items[i] : "")`
- **File:** `src/app/compile/c_runtime.c`
- **First fixed:** `qn`

### Leak 3: Option/Result no ownership
- **Cause:** `simple_some_str`/`simple_result_ok_str`/`simple_result_err_str` stored raw pointers
- **Fix:** `strdup()` on input + added `simple_option_free()` and `simple_result_free()`
- **File:** `src/app/compile/c_runtime.c`
- **First fixed:** `qn`

### Leak 4: Codegen mapped str to void*
- **Cause:** `Opaque("str")` mapped to `void*`, no string tracking
- **Fix:** Map to `const char*`, track `str_locals`, emit cleanup on reassign/return
- **Files:** `c_type_mapper.spl`, `c_backend.spl`
- **First fixed:** `rx`

### Leak 5: Generated main.c no array cleanup
- **Introduced:** `wr`
- **Cause:** No `simple_string_array_free()` definition, no atexit cleanup
- **Fix:** Added free function + `atexit(_main_cleanup)` for `_main_args`/`_main_filtered`
- **File:** `src/compiler_cpp/main.c`
- **First fixed:** `qn`

### Leak 6: Sliced arrays never freed in command dispatch
- **Introduced:** `wr`
- **Cause:** 11 `simple_string_array_slice()` results in test/build/stats/check/etc. branches never freed
- **Fix:** Store result, call handler, `simple_string_array_free()`, then return
- **File:** `src/compiler_cpp/main.c`
- **First fixed:** `qn`

### Leak 7: simple_substr_from temp strings leaked
- **Introduced:** `wr`
- **Cause:** `simple_substr_from()` returns `strdup()`'d strings for `--jit-threshold=`, `--backend=`, etc.
- **Fix:** Use pointer arithmetic (`arg + N`) instead
- **File:** `src/compiler_cpp/main.c`
- **First fixed:** `qn`

### Leak 8: run_lex_command args not freed
- **Introduced:** `wr`
- **Cause:** `get_cli_args()` returns heap array, never freed
- **Fix:** `simple_string_array_free(&args)` before return
- **File:** `src/compiler_cpp/main.c`
- **First fixed:** `qn`

### Leak 9: program_args in default branch not freed
- **Introduced:** `wr`
- **Cause:** `simple_new_string_array()` result in default file-execution branch never freed
- **Fix:** Store return code, free array, then return
- **File:** `src/compiler_cpp/main.c`
- **First fixed:** `qn`

## Verification

- **Test:** `bin/simple test/unit/memleak/c_runtime_leak_spec.spl` — 30/30 pass
- **ASan:** `ASAN_OPTIONS=detect_leaks=1 build-asan/simple <cmd>` — 42 paths, zero leaks
- **Build:** `cmake -B build-asan ... && ninja -C build-asan`

## Test File

`test/unit/memleak/c_runtime_leak_spec.spl` — 30 sspec tests covering all 9 categories.
