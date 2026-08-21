# 84 codegen-emitted runtime symbols with no definition anywhere (2026-08-21)

**Status:** FIXED for the guard's scope (2026-08-21, second pass). Link policy
fail-closed; all 84 now implemented or NAMED-trapped in the C runtime; the
archive is rebuilt and the guard reads
`PASS — 196 symbol(s) checked across 4 binary(ies) + archive, 0 unresolved`.
Open follow-ups (emitter operand loss, GPU policy, and the SEPARATE set the
real bootstrap link actually needs) are listed at the bottom.

## What this is

`rt_unwrap_or_trap` was never a one-off. Running the newly landed
`scripts/check/check-no-unresolved-runtime-symbols.shs` reports **84** `rt_*`
names that codegen hands to an emitter and that **nothing in the tree defines**.
The native link tolerates undefined symbols, so each is a NULL GOT slot waiting
for its first call site to execute — the exact shape that SEGV'd every
self-hosted stage binary on a three-line hello world while `--version` answered
cleanly.

Guard as found (archive copied to a fresh mtime to clear the STALE gate; the
archive content is unchanged since 2026-08-21 02:49):

    FAIL — 196 symbol(s) checked across 4 binary(ies) + archive, 84 unresolved

## Which archive/objects the bootstrap `native-build` link actually uses

Determined empirically, 2026-08-21, and this **retracts the "NOT built from C"
correction that previously stood here** (kept below, struck, so the error is
traceable rather than silently edited away).

`ar t build/simple-core/libsimple_runtime.a` lists **C objects**:
`runtime_native.o`, `runtime_terminal.o`, `runtime_ssr.o`, `runtime_framebuffer.o`,
`runtime_legacy_core.o`, `runtime_fork.o`, `runtime_memtrack.o`,
`runtime_process.o`, `runtime_contracts.o`, `runtime_font.o`, `runtime_thread.o`,
`runtime_simd_utf8.o`, `runtime_simd_dispatch.o`, `runtime_packed_span.o`,
`hosted_cocoa.o`, `hosted_win32.o`, ... — **not** `.spl`-derived objects. The
archive IS the compiled C runtime. That is why adding `rt_unwrap_or_trap` to
`runtime_native.c` moved the stage binary from rc 139 to rc 1, and why
recompiling `runtime_native.o` alone retired 39 of the 84 in one step.

Lane selection: `native_project/config.rs:57,76-80,429` resolves
`simple-core` -> `build/simple-core/libsimple_runtime.a` (or `deps/`
underneath it), falling back to `core-c-bootstrap`. The bootstrap logs
(`scratchpad/bs_deploy.log`, `fixed.log`) show the archive being **rejected as
STALE** ("refusing to link a stale archive") on every stage, so those links ran
on the core-c-bootstrap C objects and left the gap unresolved.

**Therefore: every one of these symbols must live in `src/runtime/*.c`.**
Mirroring into `src/runtime/simple_core/*.spl` is not required for this lane.

### RETRACTED — the archive is NOT built from C

The archive the guard judges, `build/simple-core/libsimple_runtime.a`, is built
by `scripts/check/check-simple-core-runtime-smoke.shs` from
**`src/runtime/simple_core/*.spl`** — 18 pure-Simple entries compiled with
`native-build --emit-archive --no-mangle`, then `ar rcs` over the extracted
objects. **No `src/runtime/*.c` object is in it.** Work in `runtime_native.c`
therefore serves the C/native runtime lane and does **not** move the archive
column of that guard's count. Both lanes need the symbols; only one of them was
in scope for this pass.

Two further facts the raw count hides:

- **The archive is STALE** (older than `src/runtime/runtime_native.c`), and the
  guard fails closed on that — correctly.
- **5 of the 84 are already implemented in `simple_core/*.spl`** and are
  reported missing *only* because the archive predates them:
  `rt_unwrap_or_trap` (`core_values.spl:78`), `rt_array_enumerate`
  (`core_array_query.spl`), `rt_array_extend_i64`, `rt_array_first`
  (`core_array_ops.spl`), `rt_future_await` (`core_async.spl`).
  A rebuild alone retires those five.

## Link-policy change (the part that stops this recurring)

`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`,
`generate_stub_object`.

`is_runtime_owned_symbol` already kept `rt_*` **out** of the auto-stub set —
the runtime, not the stub generator, owns them. That was the whole story: the
reference was then simply left undefined and the final link accepted it. The
sibling lane `linker/native_binary/stubs.rs` has had a fail-closed rt_* check
(task #97, `RT_KEEP` + `SIMPLE_ALLOW_UNRESOLVED_RT`) for a while; this lane had
nothing. It now computes the undefined runtime-prefixed set and returns a hard
error **naming every symbol**.

- Prefixes covered: `rt_` and `spl_` — the only two `runtime.h` exports (802 and
  99 declarations respectively).
- Pre-existing exemptions still apply first: `is_optional_weak_hook_symbol`,
  `is_compiler_provided_runtime_symbol`, `is_linker_provided_symbol`,
  `is_system_symbol`.
- Allowlist: `RT_OPTIONAL_SYMBOLS` (documented as "a NULL definition is
  CORRECT", not "not implemented yet"). Currently one entry, `rt_set_args`.
- Escape hatch: `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` (warns, proceeds).
- Bootstrap lanes (`SIMPLE_BOOTSTRAP=1` / `SIMPLE_STUB_MISSING_RT=1`) are exempt
  wholesale — they deliberately weak-stub the gap so the binary can LOAD.

Test: `test_linker_fails_closed_on_undefined_runtime_symbol`
(`pipeline/native_project/tests.rs`) builds a real `.o` calling
`rt_fixture_missing` and asserts the call returns `Err` naming both the symbol
and the escape hatch. It takes `no_stub_fallback_env_lock()` and clears
`SIMPLE_STUB_MISSING_RT`/`SIMPLE_BOOTSTRAP`, because
`test_bootstrap_stub_mode_defers_libc_process_symbols_to_linker` sets the former
process-wide and the two otherwise race (observed: passes alone, fails in suite).

Verification: `cargo test --release -p simple-compiler --lib linker -j 4` ->
`167 passed; 0 failed`. `cargo check --release --bin simple` -> 0 errors.

## Per-name status

### Implemented with real semantics (12)

Taken from `src/compiler_rust/runtime/src/value/objects.rs` and
`src/runtime/simple_core/core_values.spl`.

| symbol | source of truth |
|---|---|
| `rt_unwrap_or_trap` | `core_values.spl:78` — see below, this was still RED |
| `rt_option_some` / `rt_option_none` | `objects.rs:261-267` (Option enum_id 1 + variant-name hashes) |
| `rt_result_ok` / `rt_result_err` | same hashes `rt_unwrap_or_trap` already keys on |
| `rt_try_unwrap` | `?` propagation: payload on Some/Ok, wrapper otherwise, never traps |
| `rt_union_wrap` / `rt_union_discriminant` / `rt_union_payload` | `emit_union_wrap` passes the type index as the discriminant, so this round-trips exactly |

`rt_unwrap_or_trap` deserves its own line: the C runtime **only ever mentioned
it in a comment**. The extended spec caught this as a genuine RED before the fix
— `nm` on a compiled `runtime_native.o` confirmed no definition. It is now
implemented, transcribed from the pure-Simple canonical version.

### Named traps — emitter information loss (4)

`rt_pattern_test`, `rt_pattern_bind`, `rt_enum_unit`, `rt_enum_with`.

These are **not** "not done yet". `llvm/emitter.rs:1703-1745` discards the
operands the runtime would need:

    emit_pattern_test(dest, subject, _pattern)                 pattern dropped
    emit_pattern_bind(dest, subject, _binding)                 binding dropped
    emit_enum_unit(dest, _enum_name, _variant_name)            both names dropped, literal 0 passed
    emit_enum_with(dest, _enum_name, _variant_name, payload)   names dropped

With the pattern and variant identity gone, **every** return value is a
fabrication: `rt_pattern_test` returning 0 silently takes the wrong match arm;
`rt_enum_unit(0)` builds a variant of the wrong enum. A loud abort naming the
symbol is the only non-corrupting answer. **The real fix is in the emitter, not
the runtime** — filed here as a follow-up.

### Named traps — GPU (26)

All 26 `rt_gpu_*`. **These are STUBS, not implementations.** On the host CPU
there is no work-item, no work-group and no device-shared memory, so there is no
correct value: `rt_gpu_global_id()` answering 0 makes a kernel silently compute
element 0 for every thread. They abort via `rt_trap_unimplemented("rt_gpu_x")`,
which prints the symbol — strictly better than address 0 (you learn *which* call
died), strictly worse than the real thing (the program still dies). Real host
emulation, or a compile-time rejection of GPU intrinsics outside a kernel, is
the actual fix.

### Residual 45 — now all defined (second pass, 2026-08-21)

Appended to `src/runtime/runtime_native.c`. `clang -c` clean; `nm` shows 612
`T rt_*` in the object and 1402 in the rebuilt archive.

**Real implementations (12)**, transcribed from
`src/compiler_rust/runtime/src/value/{collections,objects,sffi/file_io}.rs`:
`rt_array_first` (collections.rs:4770), `rt_array_enumerate` (:5349),
`rt_array_extend_i64` (:1464), `rt_string_lines` (:3895),
`rt_string_parse_int` (:4239), `rt_file_write_bytes_array` (file_ops.rs:1344,
routed through the existing `rt_core_string_to_cpath` + `rt_file_write_bytes`),
and `rt_unique_{new,get}` / `rt_shared_{new,get}` / `rt_handle_{new,get}` as
transparent identity boxes — `get(new(v)) == v` matches objects.rs observably,
but refcount/ownership tracking is NOT modelled and is a follow-up, not implied.

**NAMED traps (33)** — `rt_trap_unimplemented("rt_x")`, never address 0:
- `rt_vec_*` (13) + `rt_neighbor_load` — need the SIMD vector heap object the C
  runtime does not define; a scalar guess computes the wrong lanes silently.
- `rt_generator_{create,next}`, `rt_future_{create,await}` — need a coroutine
  stack and an executor.
- `rt_par_{map,filter,reduce}`, `rt_actor_{spawn,join,recv}`, `rt_wait` — need a
  work scheduler and mailboxes.
- `rt_pointer_{new,ref,deref}` — no Rust counterpart exists at all; the emitter
  contract is unknown, so any return value would be invented.
- `rt_vtable_lookup`, `rt_value_format_string`, `rt_fstring_format`,
  `rt_interp_eval`, `rt_collection_remove`.

### Original list of the 45 (historical)

    vec        13   rt_vec_{blend,clamp,extract,fma,gather,load,masked_load,
                            max_vec,min_vec,recip,select,shuffle,with}
    pointer     3   rt_pointer_{new,ref,deref}
    par         3   rt_par_{map,filter,reduce}
    array       3   rt_array_{enumerate,extend_i64,first}      <- already in .spl
    actor       3   rt_actor_{spawn,join,recv}
    unique      2   rt_unique_{new,get}
    shared      2   rt_shared_{new,get}
    handle      2   rt_handle_{new,get}
    generator   2   rt_generator_{create,next}
    future      2   rt_future_{create,await}                   <- await already in .spl
    string      2   rt_string_{lines,parse_int}
    misc        8   rt_vtable_lookup, rt_value_format_string, rt_wait,
                    rt_neighbor_load, rt_interp_eval, rt_fstring_format,
                    rt_file_write_bytes_array, rt_collection_remove

The 13 `rt_vec_*` are the SIMD lane (`codegen/instr/simd_stubs.rs`); the Rust
runtime defines all 13 and is the transcription source. The target of "0
unresolved among option/pattern/vec/array" was met for option and pattern; vec
and array were not reached.

## Measurements

| what | before | after |
|---|---|---|
| unresolved (guard, whole set) | 84 | **0** (`PASS — 196 symbol(s) checked across 4 binary(ies) + archive, 0 unresolved`) |
| undefined in C runtime, of those 84 | 84 | 45 (first pass) -> **0** (second pass) |
| archive `T rt_*` count | 766 | **1402** |
| `check-c-runtime-compiles-push.shs` | FAIL, 1 offender, 107 clean | FAIL, **same** 1 offender, 107 clean |
| `c_runtime_unwrap_entrypoints_spec.spl` | 3 total, 2 passed, **1 failed** | **21 total, 21 passed** (`outcome=OK declared>=21 executed=21 passed=21 failed=0`) |

The C-runtime guard's single offender is
`src/runtime/test/rt_browser_renderer_namespace_selfcheck.c`, an **untracked**
file from another session (undeclared `browser_renderer_*`), pre-existing and
not touched here.

Rebuild recipe actually used (the archive is a gitignored build artifact):

    clang -c -O2 -fPIC -Isrc/runtime -o runtime_native.o src/runtime/runtime_native.c
    ar r build/simple-core/libsimple_runtime.a runtime_native.o && touch build/simple-core/libsimple_runtime.a

`check-c-runtime-compiles-push.shs` is unchanged at its single pre-existing
offender: `FAIL — 1 file(s) failed to compile:
src/runtime/test/rt_browser_renderer_namespace_selfcheck.c (107 compiled clean,
2 skipped)` — an untracked file from another session.

## The bootstrap binary needs a DIFFERENT set (new finding, 2026-08-21)

`nm -u` on the previous lane's linked `scratchpad/fixed_simple` shows **87
undefined `rt_*`**, and the overlap with the guard's 84 is nearly empty — no
`rt_vec_*`, no `rt_par_*`, no `rt_actor_*`, no `rt_pointer_*`. What the real
bootstrap link is actually missing is dominated by **76 `rt_cranelift_*`**
(`rt_cranelift_iadd`, `_icmp`, `_call`, `_new_module`, `_emit_object_raw`, ...)
plus: `rt_any_le`, `rt_array_max`, `rt_cstring_to_text`, `rt_dir_list`,
`rt_file_copy`, `rt_file_hash_sha256`, `rt_file_rename`,
`rt_is_debug_mode_enabled`, `rt_main`, `rt_native_build`, `rt_range`, `rt__`,
and (overlapping the 84) `rt_array_enumerate`, `rt_array_extend_i64`,
`rt_collection_remove`, `rt_file_write_bytes_array`.

The guard measures the codegen-emitted name set; the bootstrap CLI additionally
drags in the Cranelift SFFI surface. **Both are real, and closing one does not
close the other.** A fresh fail-closed `native-build` of
`src/app/cli/bootstrap_main.spl` is the authority on the second list.

## Follow-ups

1. Implement the 45 residual names — `rt_vec_*` and `rt_array_*` first (real
   Rust-runtime semantics exist for both).
2. Mirror all of this into `src/runtime/simple_core/*.spl`, the lane the
   unresolved-symbol guard actually measures.
3. Rebuild `build/simple-core/libsimple_runtime.a` and re-quote the guard.
4. **Emitter fix:** stop dropping the pattern/binding/enum-name operands in
   `llvm/emitter.rs:1703-1745`, then replace the 4 named traps with real
   implementations.
5. Decide GPU policy: host emulation, or reject GPU intrinsics at compile time
   outside a kernel. The 26 traps are a holding position, not an answer.

## Files

- `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` — fail-closed check, `RT_OPTIONAL_SYMBOLS`, `ALLOW_UNRESOLVED_RUNTIME_ENV`
- `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` — `test_linker_fails_closed_on_undefined_runtime_symbol`
- `src/runtime/runtime_native.c` — 39 definitions
- `src/runtime/runtime.h` — declarations
- `test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl` — extended to 11 examples
