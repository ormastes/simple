# Seed interpreter-extern registry census (2026-08-23)

Measured at `origin/main` 6c78a408f8d, after the `rt_heap_ref_wellformed` fix
(`fc25bd463a4`, `fa4ca4aa7f9`) had landed. Every number below comes from that tree.

## Method

- **Declared**: `extern fn rt_*` under `src/compiler/**/*.spl` — the externs the
  seed must resolve to interpret the compiler's own sources. **282 distinct.**
- **Registered**: names carrying a static `insert*!("rt_...", ...)` row in
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`. **1,504.**
  Extraction folds newlines first: rustfmt wraps many rows across lines and a
  single-line regex under-counts by ~150, manufacturing false offenders.
- **Backed**: `nm -g --defined-only`, not text-grep, over two real link
  artifacts built from this tree: the Rust runtime staticlib
  (`cargo build --release -p simple-runtime`, rc=0 -> `libsimple_runtime.a`,
  1,959 defined `rt_*`) and objects compiled from every owned `src/runtime/**.c`
  (114 compiled, 6 failed on unavailable external SDK headers; 1,407 defined
  `rt_*`). Union: **2,491 defined `rt_*` symbols.**
- **RUNTIME_SYMBOL_NAMES**: `src/compiler_rust/common/src/runtime_symbols.rs`
  lines 390-2358. **1,745.**

## Result

| set | count |
|---|---|
| externs declared under `src/compiler/**` | 282 |
| ... with a static `interpreter_extern` row | 167 |
| ... **without** one (the gap) | **115** |
| gap symbols DEFINED in a real runtime artifact (nm) | **30** |
| gap symbols defined nowhere (unbacked-extern class) | 85 |
| `RUNTIME_SYMBOL_NAMES` entries absent from `interpreter_extern` | 800 |

**Not a measured zero.** `rt_heap_ref_wellformed` was one of a class, and 30
further compiler-declared externs are defined in a real runtime artifact yet
have no interpreter registry row — the same shape that blocked phase 1:

- `rt_actor_recv`
- `rt_actor_send`
- `rt_actor_spawn`
- `rt_array_push_i64_raw`
- `rt_close_fd`
- `rt_heap_peak_bytes`
- `rt_madvise`
- `rt_madvise_raw`
- `rt_memcmp`
- `rt_mlock`
- `rt_mmap`
- `rt_msync`
- `rt_msync_flags`
- `rt_munlock`
- `rt_munmap`
- `rt_open_fd`
- `rt_page_size`
- `rt_path_parent`
- `rt_print_value`
- `rt_println`
- `rt_println_value`
- `rt_realloc`
- `rt_shell_output`
- `rt_string_contains`
- `rt_string_index_of`
- `rt_string_replace`
- `rt_string_starts_with`
- `rt_string_trim`
- `rt_text_eq_any`
- `rt_value_eq`

The other 85 are declared but defined nowhere at all. That is the
`unregistered_extern_silent_nil_2026-08-01` population, already frozen by
`scripts/check/unbacked_extern_baseline.txt`; they are reported here and
deliberately **not** double-gated.

## Honest limit on the 30

A missing static row is **not** proof the seed fails on the symbol. The
dispatcher (`interpreter_extern/mod.rs:2955-2991`) falls through to prefix
families (`rt_driver_`, `rt_vulkan_`), a capability-gap arm, and finally
`dynamic_sffi::try_call_dynamic`, a dlopen resolver. Some of the 30 —
`rt_string_contains`, `rt_string_trim`, `rt_println` — are also reachable
through codegen alias maps (`codegen/instr/calls.rs:3090` maps
`rt_string_contains` -> `rt_contains`). So the list is an upper bound on the
risk, and the right verdict is "30 candidates, none currently blocking",
not "30 broken symbols". Confirming each one requires running the seed and
reading the error text; that was not done for all 30 here.

## Why the gate is a ratchet, not `runtime_symbols.rs` parity

The open item filed with the other lane's fix was "no parity gate between
`interpreter_extern` and `runtime_symbols.rs`". Full parity is the wrong
invariant: **800** `RUNTIME_SYMBOL_NAMES` entries are absent from the
interpreter registry, and most are codegen-only entry points the interpreter
never dispatches. A guard asserting parity would be red on day one for
non-defects and would get routed around. So
`scripts/check/check-interpreter-extern-registry-gap.shs` freezes the 115-symbol
gap in `scripts/check/interpreter_extern_gap_baseline.txt` and fails on any NEW
unregistered compiler extern, and on any stale baseline row, in both
directions — the `check-unbacked-extern-ratchet.shs` pattern. The 800 figure is
recorded in the guard header rather than gated.
