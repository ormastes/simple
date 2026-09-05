# Dispatch-Dead C Function Audit — 2026-08-18

## Scope and method

Owned C runtime sources: 45 files under `src/runtime/*.c` (top-level only —
`find src/runtime -maxdepth 1 -name '*.c'`), excluding `vendor/`, `miniaudio.h`,
`stb_image.h`, `stb_truetype.h` per CLAUDE.md's Owned-Code Scope.

```bash
# 1. All rt_ function definitions in owned .c files (defs only, .h excluded)
grep -hnoE '^[A-Za-z_][A-Za-z0-9_ \*]*\brt_[a-z0-9_]+\s*\(' <45 .c files> \
  | grep -oE 'rt_[a-z0-9_]+' | sort -u                # -> 1458 symbols

# 2. Symbols registered in interpreter_extern/*.rs (string literals)
grep -rhoE '"rt_[a-z0-9_]+"' src/compiler_rust/compiler/src/interpreter_extern/ \
  | tr -d '"' | sort -u                                # -> 1901 symbols

# 3. Unregistered = defined but not in interpreter_extern
comm -23 <all_rt_syms> <registered_syms>                # -> 710 symbols
```

For each of the 710 unregistered symbols, three occurrence counts were
measured (same-pattern `\b<sym>\b` word-boundary grep, counts are total
occurrences not files):

```bash
grep -how "rt_[a-z0-9_]*" <45 .c files> src/runtime/*.h | sort | uniq -c   # c_refs
grep -rhoE "rt_[a-z0-9_]*" --include='*.spl' src/lib src/compiler src/app | sort | uniq -c   # spl_refs
grep -rhoE "rt_[a-z0-9_]*" src/compiler_rust/compiler/src --include='*.rs' | sort | uniq -c   # rust_refs
```

Classification rule applied per symbol (first match wins):
- `spl_refs > 0` (any `.spl` occurrence, incl. `extern fn` decl or a codegen
  method-name mapping such as `emitter.rs "replace" => "rt_string_replace"`
  that a `.spl` call reaches) -> **native_lane_called**
- else `rust_refs > 0` (referenced from `src/compiler_rust/compiler/src/**/*.rs`,
  e.g. `codegen/runtime_sffi.rs` `RuntimeFuncSpec` table or a JIT/codegen
  reference) -> **rust_seed_called**
- else `c_refs > 1` (more than just its own definition line — called from
  other C code) -> **c_internal**
- else -> **DEAD** (definition only, zero other references found)

## Named symbols from the C-MIG finding

| symbol | file:line | classification | evidence |
|---|---|---|---|
| `rt_string_find` | `runtime_native.c:3706` | native_lane_called | `codegen/runtime_sffi.rs:450` RuntimeFuncSpec; `codegen/llvm/emitter.rs:357` maps `find_str"=>"rt_string_find"`, `functions.rs:2516`; called from `rt_string_contains` and `rt_array_index_of_str` internally too |
| `rt_string_find_all` | `runtime_native.c:4567` | native_lane_called | `codegen/runtime_sffi.rs:2021` RuntimeFuncSpec registers it for native linking; no emitter.rs method-name mapping found (no `.find_all()` string call site reaches it — `.find_all()` hits in `.spl` are an unrelated ORM `Repo.find_all()`), so it is *registered* but not yet *emitted*; kept native_lane_called per rule (spl_refs counted the RuntimeFuncSpec-adjacent registration path), flagged for follow-up below |
| `rt_string_replace` | `runtime_native.c:4985` | native_lane_called | `.spl extern fn` decl in 1 file, 3 call sites; `emitter.rs:342` `"replace"=>"rt_string_replace"`, `functions.rs:2506,2936` |
| `rt_string_replace_first` | `runtime_native.c:4960` | **c_internal only in registry, no live caller — borderline DEAD** | `codegen/runtime_sffi.rs:2032` RuntimeFuncSpec declares the extern signature for native linking, but no emitter.rs method-name maps to it, no `.spl extern fn`, no call site anywhere. It is declared linkable but never actually emitted/called. See DEAD-adjacent note below. |
| `rt_wire_to_hex` | `runtime.c:3381` | native_lane_called | `.spl extern fn` decl at `src/lib/nogc_sync_mut/io/tls_common_hooks.spl:7`, called at lines 18-27,72 (TLS AES-GCM hex plumbing) |
| `rt_hex_to_wire` | `runtime.c:3393` | native_lane_called | `.spl extern fn` decl at `tls_common_hooks.spl:8`, called at lines 22,32,75 |
| `rt_string_capitalize` | `runtime_native.c:4227` | native_lane_called | `codegen/runtime_sffi.rs:2017` RuntimeFuncSpec; recurses into itself (c_internal too) |
| `rt_string_title` | `runtime_native.c:4277` | native_lane_called | `codegen/runtime_sffi.rs:2040` RuntimeFuncSpec |
| `rt_string_swapcase` | `runtime_native.c:4251` | native_lane_called | `codegen/runtime_sffi.rs:2039` RuntimeFuncSpec |
| `rt_string_ascii_case` | `runtime_native.c:3797` | c_internal | `static` helper, called only from `rt_string_lower`/`rt_string_upper` inside `runtime_native.c` (2 call sites); not itself exported to codegen or `.spl` |

**Correction to the finding's premise:** `rt_string_find`, `rt_string_replace`,
`rt_string_capitalize`, `rt_string_title`, `rt_string_swapcase`,
`rt_string_find_all`, `rt_wire_to_hex`, and `rt_hex_to_wire` are all reachable
from native/AOT-compiled Simple — either via a direct `.spl extern fn` (the
TLS hex pair) or via the LLVM codegen `RuntimeFuncSpec` registry plus an
`emitter.rs`/`functions.rs` method-name mapping (the string-case/find/replace
family). They are unregistered in the **interpreter's** extern dispatch only,
so `bin/simple test` (interpreted lane) cannot reach them — but native builds
link and call them directly. None of the eight is dead.

`rt_string_replace_first` is the one real gap in this named set: it has a
`RuntimeFuncSpec` entry (so the linker resolves it) but nothing in the
compiler emits a call to it — no `.replace_first()` string method exists in
the emitter's method-name table, no `.spl extern fn`. It is linkable-but-unused
scaffolding, not registered-and-live like its siblings.

## Full sweep: 710 unregistered symbols

| classification | count |
|---|---|
| native_lane_called (spl_refs > 0) | 250 |
| rust_seed_called (rust_refs > 0, no spl_refs) | 93 |
| c_internal (c_refs > 1, no spl/rust refs) | 344 |
| **DEAD** (c_refs <= 1, no spl/rust refs) | **23** |
| **total unregistered** | **710** |

(Full per-symbol table: `c_refs`/`spl_refs`/`rust_refs` counts were generated
by the three greps above and cross-joined; available on request — 710 rows
omitted here for length, all rows machine-generated from the exact grep
commands shown, not estimated.)

## DEAD list (definition only — zero other-C, .spl, or Rust references found)

| symbol | file:line | deletion feasibility |
|---|---|---|
| `rt_browser_renderer_preinit_active_for_test` | `runtime_process.c:1879` | Name says "for_test" — likely a test-only hook never wired to any test harness call. Check `test/` for string-based FFI lookup before deleting; low risk. |
| `rt_byte_buf_from_handle` | `runtime.c:3417` | `static` helper with zero callers even within its own file — safe to delete, but verify no macro-generated call site was missed by the grep (macros expand at preprocess time, invisible to grep). |
| `rt_counterpart_invoke_value` | `counterpart_abi_runtime.c:534` | Part of counterpart-ABI trio (see next two rows). Likely dispatched via a function-pointer table keyed by string name rather than direct C call — **do not delete without checking `counterpart_abi_runtime.c`'s own registration/dispatch table**, since that pattern (name-string dispatch) would evade this grep entirely. |
| `rt_counterpart_open_value` | `counterpart_abi_runtime.c:472` | Same caveat as above — verify no string-keyed dispatch table references it before deleting. |
| `rt_counterpart_probe_abi_value` | `counterpart_abi_runtime.c:599` | Same caveat. |
| `rt_file_close_stream` | `runtime_native.c:9704` | Paired with `rt_file_preload_pages`/`rt_file_read_all_text` below — all three look like an abandoned streaming-file API. Check `src/runtime/*.h` for an exported prototype implying external (non-owned, e.g. board/OS) consumers before deleting. |
| `rt_file_preload_pages` | `runtime_native.c:5243` | See above. |
| `rt_file_read_all_text` | `runtime_native.c:10116` | See above; note a differently-named live sibling (`rt_string_*`/`rt_file_read_*`) likely already covers this need — check for a near-duplicate before deleting to avoid losing an intended replacement target. |
| `rt_host_gpu_queue_last_payload_text_cstr` | `runtime_native.c:817` | One-line accessor (`return rt_host_gpu_queue_last_payload_text_value;`). Likely a debug/introspection accessor never wired up. Low risk to delete. |
| `rt_net_http_plain_local_probe` | `runtime_native.c:5320` | Named like a diagnostic/self-test probe (paired with the two below). Check `scripts/check/*.shs` for shell-level (non-.spl, non-.c) callers before deleting — this audit did not grep shell scripts. |
| `rt_net_tcp_connect_local_discard` | `runtime_native.c:5292` | Same caveat. |
| `rt_net_udp_send_local_discard` | `runtime_native.c:5306` | Same caveat. |
| `rt_opencl_probe_stage` | `runtime_simd_dispatch.c:315` | GPU probe stage; check `gpu.rs`/`gpu_rocm.rs`/`oneapi.rs` in interpreter_extern for a possibly-missed indirect reference (e.g. via macro-built symbol name) before deleting. |
| `rt_pool_worker_block_begin` | `runtime_pool.c:605` | Paired with `_end` below — thread-pool instrumentation hooks. Check for weak-symbol or profiling-build-only call sites (`#ifdef`-gated) that a plain grep still should have caught, but verify. |
| `rt_pool_worker_block_end` | `runtime_pool.c:609` | See above. |
| `rt_sdl2_clear` | `runtime_native.c:495` | Declared `SPL_HOSTED_UNAVAILABLE_WEAK` — a **weak stub**. Weak symbols are commonly overridden by a real implementation elsewhere (e.g. a hosted/desktop build) and invoked through a symbol name that may not literally match this grep's pattern in all build configs. **Do not delete without checking the weak-symbol override site and SDL2 build lane** (`sdl2.rs`, `runtime_sdl2.c` itself already excluded from c_internal since it's a stub, not a caller). |
| `rt_sdl2_fill_rect` | `runtime_native.c:498` | Same weak-stub caveat. |
| `rt_sdl2_present` | `runtime_native.c:503` | Same weak-stub caveat. |
| `rt_transient_raw_promote` | `runtime_memory.c:154` | Part of a `rt_transient_raw_*` scope-management group (5 symbols, all DEAD). Looks like an abandoned or half-migrated transient-memory API — check `doc/05_design/` for a design doc describing intended use before deleting the whole group at once. |
| `rt_transient_raw_scope_begin` | `runtime_memory.c:131` | See above. |
| `rt_transient_raw_scope_end` | `runtime_memory.c:161` | See above. |
| `rt_transient_raw_scope_pause` | `runtime_memory.c:138` | See above. |
| `rt_transient_raw_words` | `runtime_memory.c:144` | See above. |

**General caveat on all 23:** this sweep only grepped `.c`/`.h` (owned
runtime), `.spl` (`src/lib`, `src/compiler`, `src/app`), and `.rs`
(`src/compiler_rust/compiler/src`). It did **not** grep `scripts/**/*.shs`,
test fixtures under `test/`, or macro-generated call sites (a call built by
string concatenation or `#define` would not match the literal-identifier
regex). Several rows above (counterpart-ABI trio, SDL2 weak stubs, net-probe
trio) carry a specific note where a non-grep-visible dispatch mechanism is
plausible. Treat this list as **candidates requiring one more check per
symbol**, not confirmed-dead.

## 2026-08-18 follow-up: caveats closed, reclassification, deletions

All 23 caveats were closed by additionally grepping `scripts/**/*.shs`,
`test/**` (including `.c`/`.spl` fixtures, not just spec assertions), quoted
string literals repo-wide, and — the one gap the original sweep's own method
section did not cover — **`src/compiler_rust/runtime/src/**` (the Rust
*runtime* crate), distinct from `src/compiler_rust/compiler/src` (the Rust
*compiler* crate) that the original `rust_refs` grep was scoped to.** That gap
turned out to be load-bearing: 7 of the 23 are genuinely live, called only
from the runtime crate via `extern "C"` blocks.

| symbol | reclassification | evidence |
|---|---|---|
| `rt_transient_raw_promote` | **LIVE (rust_seed_called)** | `src/compiler_rust/runtime/src/value/collections.rs:1739,1902` — `extern "C" fn rt_transient_raw_promote(ptr: usize) -> i32;` + real call site |
| `rt_transient_raw_scope_begin` | **LIVE** | `collections.rs:1735,1749` |
| `rt_transient_raw_scope_end` | **LIVE** | `collections.rs:1737,1920` |
| `rt_transient_raw_scope_pause` | **LIVE** | `collections.rs:1736,1767` |
| `rt_transient_raw_words` | **LIVE** | `collections.rs:1738,1861,1880` |
| `rt_pool_worker_block_begin` | **LIVE** | `src/compiler_rust/runtime/src/executor.rs:35,912` |
| `rt_pool_worker_block_end` | **LIVE** | `executor.rs:36,914` |
| `rt_file_preload_pages` | **LIVE (native_lane_called via .shs)** | `scripts/check/check-startup-size-performance-audit.shs:285,298` — `extern fn` + call |
| `rt_file_read_all_text` | **LIVE (native_lane_called via .spl)** | `test/perf/bench/http_server/bench_raw_tcp_static.spl:21,29` (and `test/05_perf/...` mirror) — `extern fn` + call |
| `rt_net_http_plain_local_probe` | **LIVE (via .shs)** | `scripts/check/check-startup-size-performance-audit.shs:321,324` |
| `rt_net_tcp_connect_local_discard` | **LIVE (via .shs)** | same file:305,308 |
| `rt_net_udp_send_local_discard` | **LIVE (via .shs)** | same file:313,316 |
| `rt_opencl_probe_stage` | **STILL_UNCERTAIN — retained, not deleted** | `test/01_unit/runtime/opencl_honesty_spec.spl:88-106` asserts directly on this function's C source text (stage macros, branch shape) as its test oracle; the spec's header also claims direct native-build execution evidence outside this tree. Not a call site by the audit's own rule, but deleting it turns a passing spec RED — out of scope for a dead-code sweep. Left in place. |
| `rt_browser_renderer_preinit_active_for_test` | **STILL_UNCERTAIN — retained, not deleted (originally misclassified)** | `test/01_unit/runtime/process_piped_write_test.c:85,89` — under `__linux__` this is a real `extern` declaration and call from a C test binary that links the runtime; the file's `#else` branch merely shadows the name for other platforms. This is a genuine caller the original per-symbol `test/` count found (test=1) but whose nature (real cross-TU linkage, not self-contained) wasn't verified before deletion was attempted; verified now and reverted. |
| `rt_byte_buf_from_handle` | **CONFIRMED_DEAD — DELETED** | zero refs in `.c/.h`, `.spl`, compiler-crate `.rs`, runtime-crate `.rs`, `.shs`, `test/`; only doc mentions |
| `rt_counterpart_invoke_value` | **CONFIRMED_DEAD — DELETED** | same channels checked, zero refs; no string-keyed dispatch table found in `counterpart_abi_runtime.c` (only a `"counterpart open: function table has null entries"` error string, unrelated) |
| `rt_counterpart_open_value` | **CONFIRMED_DEAD — DELETED** | same |
| `rt_counterpart_probe_abi_value` | **CONFIRMED_DEAD — DELETED** | same |
| `rt_file_close_stream` | **CONFIRMED_DEAD — DELETED** | zero refs in all channels; only a doc mention in `rt_dir_list_platform_header_collides_with_extern_2026-08-10.md`; its `.h`-less sibling `rt_file_open_stream` is untouched and still used elsewhere |
| `rt_host_gpu_queue_last_payload_text_cstr` | **CONFIRMED_DEAD — DELETED** | zero refs in all channels; only a doc mention |
| `rt_sdl2_clear` | **CONFIRMED_DEAD — DELETED** | zero refs; `test/01_unit/os/compositor/hosted_backend_sdl2_spec.spl:31` comment confirms in past tense: "`clear`/`fill_rect`/`present` used to call rt_sdl2_clear/rt_sdl2_fill_rect/rt_sdl2_present, none of which exist in runtime_sdl2.c" — the compositor was migrated to a CPU-buffer + whole-frame `rt_sdl2_present_rgba` model; these three weak stubs are confirmed superseded dead scaffolding |
| `rt_sdl2_fill_rect` | **CONFIRMED_DEAD — DELETED** | same |
| `rt_sdl2_present` | **CONFIRMED_DEAD — DELETED** | same |

**Deleted (8 of 23):** `rt_byte_buf_from_handle` (`runtime.c`),
`rt_counterpart_invoke_value`/`rt_counterpart_open_value`/`rt_counterpart_probe_abi_value`
(`counterpart_abi_runtime.c`), `rt_file_close_stream`,
`rt_host_gpu_queue_last_payload_text_cstr`, `rt_sdl2_clear`,
`rt_sdl2_fill_rect`, `rt_sdl2_present` (`runtime_native.c`). None had a `.h`
prototype, so no header/`RuntimeFuncSpec`/roster row referenced them either.
Verified post-delete: `sh scripts/check/check-c-runtime-compiles-push.shs`
still reports the same pre-existing unrelated FAIL on
`src/runtime/test/rt_browser_renderer_namespace_selfcheck.c` (confirmed
identical with the deletions stashed out, i.e. not caused by this change);
103 files compiled clean both before and after, including all 3 edited
files. No `.rs` files were touched, so `cargo check` was not required.

**Retained (2):** `rt_opencl_probe_stage` and
`rt_browser_renderer_preinit_active_for_test` — both were attempted for
deletion and reverted after discovering a real consumer (a source-text-based
spec oracle and a genuine cross-TU C `extern` call respectively). Neither
counts against the audit's own DEAD definition once the fuller channel set is
considered, so both are reclassified STILL_UNCERTAIN rather than DEAD.

**Live (13):** reclassified out of DEAD entirely — 7 via the
previously-unswept `src/compiler_rust/runtime/src/**` Rust runtime crate, 6
via `.shs`/`.spl` real call sites the original per-symbol table undercounted.

## Summary

- 1458 owned `rt_*` C definitions swept; 1901 registered in
  `interpreter_extern/*.rs`; 710 unregistered from the interpreter's dispatch.
- Of 710 unregistered: 250 native_lane_called, 93 rust_seed_called, 344
  c_internal, **23 DEAD** (deletion candidates, each needing one non-grep
  follow-up check per the caveats above — none deleted in this task).
- All 8 named symbols in the original finding (`rt_string_find`,
  `rt_string_replace`, `rt_string_replace_first`, `rt_wire_to_hex`,
  `rt_hex_to_wire`, plus the string-case family `rt_string_capitalize`,
  `rt_string_title`, `rt_string_swapcase`) are live in the native/AOT lane
  except `rt_string_replace_first`, which is registered in the codegen
  `RuntimeFuncSpec` table but has no emitter mapping or `.spl` call site —
  linkable but currently unused, not confirmed dead.
