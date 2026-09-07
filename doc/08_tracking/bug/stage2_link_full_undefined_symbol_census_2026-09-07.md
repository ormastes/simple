# Stage2 bootstrap link: complete undefined-symbol census (2026-09-07)

## Problem

Stage2 of `scripts/bootstrap/bootstrap-from-scratch.sh` (aarch64 host, the
`core-c-bootstrap` runtime-bundle lane — `native-build --runtime-bundle
core-c-bootstrap` on `src/app/cli/bootstrap_main.spl`'s full closure) failed to
link across runs 20/21/22 (`build/memlog/bootstrap_full{20,21,22}.log`). Each
run's diagnosis tool truncates to "First 5" lines
(`scripts/check/check-stage-log-diagnosable.shs`), and — more importantly —
**LLD itself stops at its default `--error-limit=20`** (confirmed: the real
log ends `ld: error: too many errors emitted, stopping now (use
--error-limit=0 to see all errors)`). So each run only ever revealed ~18-20
distinct symbols; fixing them let compilation/linking reach further and
reveal a new batch, producing a whack-a-mole loop.

## How completeness was established

1. The failed link's kept object set survived on disk:
   `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/native-objects-8HIZif/`
   (run22, `Link failed. Objects kept at: ...`), containing `spl_objects.rsp`
   (861 compiled `.spl`-program objects), the core-C runtime archive
   (`bootstrap_mutex_core_c_runtime/libsimple_runtime.a`, 25 members), the
   Rust "mutex capsule" archive, `_init_all.o`/`_main_stub.o`/`_stubs.o`, and
   `link-compat/libunwind.so`.
2. Reproduced the exact link with `clang++ @spl_objects.rsp ... -Wl,--error-limit=0`
   (real linker, real inputs, no bootstrap re-run). Result: **246 distinct
   `undefined symbol:` lines**, 0 duplicate-symbol errors.
3. Cross-checked with an independent method per the task's option 3: `nm -u`
   over every `mod_*.o` minus every symbol *defined* anywhere in the same
   object set, the runtime archives, `/lib/aarch64-linux-gnu/{libc,libm,libz,
   libzstd,libtinfo,libstdc++,libgcc_s}.so*` (dynamic exports via `nm -D
   --defined-only`), and `link-compat/libunwind.so`. Result: 247 symbols —
   exactly the same set plus `raise` (a libc symbol version-decoration false
   positive in the `nm` approach; the real linker resolves it fine). The two
   methods agree on all 246 symbols the linker actually reports, which is
   the completeness proof: `comm -23` between them is empty in both
   directions except that one explained false positive.
4. No `bootstrap-from-scratch.sh` process was running against this tree at
   analysis time (`pgrep -fa bootstrap-from-scratch` empty; the log's mtime
   matched run22's recorded failure time exactly), so the object set was a
   stable, non-moving target — read-only, never modified.

## Classification (246 symbols total)

Bucket definitions per the task:
1. **Unbacked extern** — declared, implemented in neither C nor Rust.
2. **C-only-vs-lane-gap** — implemented on one side (C or Rust) but not
   reachable from *this* archive/lane.
3. **Resolve-by-name miscompile** — UFCS/method-call codegen resolved to a
   name nothing defines (dotted symbols: `Type.method`).
4. **Genuinely missing / lenient-unresolved-global** — HIR lowering produced
   an unresolved identifier that `lenient_types` silently lowered to an
   undefined global reference (same mechanism the original log's `note:`
   block documents for `Unit`).

| Bucket | Count | Disposition |
|---|---|---|
| FIXED (1/2, mechanical) | 32 | Implemented this change — see below |
| 1-candidate, no reference semantics | 15 | `rt_file_view_*_v1` (9), `rt_pinned_archive_*_v1` (5), `rt_native_build` (1) — 0 C, 0 Rust *native* symbol, and no header/doc contract exists to mirror. Handed off. |
| 2-deferred: cranelift JIT bridge | 75 | `rt_cranelift_*` — implemented in Rust (`codegen/cranelift_sffi.rs`, `interpreter_extern/cranelift.rs`) for the seed's own JIT; this archive is a plain native-AOT C lane with no JIT concept. Handed off — needs a design decision (stub vs. exclude the JIT-only call sites from this closure), not a mechanical port. |
| 2-deferred: sqlite lane wiring | 24 | `rt_sqlite_*` — **deliberately excluded** from the core-C archive by design (`build_sqlite_runtime_object`'s doc comment in `native_project/tools.rs`: avoids forcing `-lsqlite3` on every native binary). The real bug is the caller not detecting sqlite usage and adding the on-demand object + `-lsqlite3` for *this* closure. Lane-wiring bug, not a runtime gap. Handed off. |
| 2-deferred: Rust-only, C-lane gap (misc) | 90 | Implemented in Rust (`runtime/src/value/**`, mostly `#[no_mangle] extern "C" fn`) but never ported to the core-C-bootstrap archive: `rt_file_*`/`rt_io_file_*` (file I/O), `rt_log_*`, `rt_random_*`, `rt_path_*`, `rt_env_*`, `rt_process_*`, `rt_dir_glob`, `rt_exec`, `rt_execute_native`, `rt_fs_read_text`, `rt_get_host_target_code`, `rt_array_sum`/`rt_array_sorted`, `rt_cli_handle_compile`/`rt_cli_run_tests_process_args`, `rt_mem_attr_*`, `rt_typed_bytes_u8_data_at`, the `rt_simd_*` SIMD-intrinsic family (add/sub/mul/and/or/xor/shl/shr over i32x4/i32x8/u8x16, AES round, carryless-multiply, xor_u64x2). Real bucket-2 debt, same shape as the fixed set, but 90 symbols is too large to port safely and individually-verify in this change's scope — each needs its own semantics check (e.g. the SIMD family needs intrinsic-level correctness, not just a libm passthrough). Handed off with this census as the punch list. |
| 3: UFCS/method resolve-by-name | 7 | `Array.remove_at`, `CompilerDriver.compile_to_vhdl`, `DynamicBackendPluginLease.admitted_handle`, `GenericTemplate.is_err`, `MirBuilder.emit_comment`, `str.split_whitespace`, `str.strip`. Owned by the UFCS classifier agent already working this per the task's instructions — not touched here. |
| 4: lenient-unresolved-global | 3 | `Unit`, `virtual_source_store`, `rt_numeric.f64` — same `lenient_types` HIR-fallback mechanism as `Unit`'s documented `note:` block. |

Table counts: 32+15+75+24+90+7+3 = 246, matching the linker's own count exactly.

**Not one of the 246, but flagged for the same owner:** `raise` appeared as
undefined in the naive `nm -u` census (method #3 above) but is *not* in the
real linker's list — it resolves fine because `raise` also happens to be a
real libc symbol (`raise(int)`, POSIX signal-raise), and this archive links
against `libc.so`. That is a **latent miscompile risk, not a link failure**:
a bare Simple-level `raise` identifier that HIR lowering could not resolve
silently fell through to whatever `raise` the system linker could find,
rather than failing loudly. Flagged for the UFCS/resolution owner alongside
`Unit` and the other `lenient_unresolved_global` cases, since the underlying
mechanism is the same — it just happens not to break *this* link.

## What was implemented (buckets 1 and 2 only, mechanical/safe)

All added to `src/runtime/runtime_native.c` (already an archive member of
`bootstrap_mutex_core_c_runtime`/`build_core_c_runtime_library`'s core-C
bootstrap archive — no whitelist change needed, no new file, no risk of the
"`runtime.c`/`runtime_native.c` collide with Rust-owned rt_* APIs" class of
regression this file's own comments warn about elsewhere), plus
`rt_time_monotonic_ns` mirrored into `src/runtime/runtime_time.c` for the
parallel Rust-hosted lane (`build.rs`'s C-source whitelist already carries
`runtime_time.c`; that lane never had this symbol under this name either).

- **`rt_time_monotonic_ns`** (genuinely missing: 0 C, 0 Rust *native* symbol
  — the Rust `interpreter_extern::time::rt_time_monotonic_ns` found by grep is
  an interpreter-dispatch shim, `fn(&[Value]) -> Result<Value, CompileError>`,
  never a linkable `#[no_mangle] extern "C" fn`). Implemented as a plain
  alias of the existing `rt_time_now_ns()`/`rt_time_now_nanos()` in each file
  — both already `clock_gettime(CLOCK_MONOTONIC, ...)`-backed, never
  wall-clock, matching the task's explicit semantics requirement.
- **11 `rt_math_*` libm passthroughs** (`asin acos atan atan2 sinh cosh tanh
  floor ceil log log10 log2`) — implemented in Rust
  (`runtime/src/value/sffi/math.rs`, one-line `f64::x()` wrappers) but not in
  C anywhere; mirrored as direct `<math.h>` calls, identical to the
  pre-existing `rt_math_pow` immediately above them in the same file.
- **`rt_simple_abi_version` / `rt_simple_abi_version_deferred`** — *do*
  exist in `runtime.c` (lines 35-41) but that file is wholesale-excluded
  from this archive (documented collision risk with Rust-owned `rt_*` APIs).
  Verbatim mirror of the two one-line reads of the `SIMPLE_ABI_VERSION`/
  `SIMPLE_ABI_VERSION_DEFERRED` macros `runtime.h` already defines and
  `runtime_native.c` already includes.
- **Full `rt_atomic_int_*` / `rt_atomic_bool_*` family** (17 symbols:
  int store/swap/fetch_add/fetch_sub/fetch_and/fetch_or/fetch_xor/free, bool
  new/load/store/swap/compare_exchange/free/fetch_and/fetch_or/fetch_not).
  `runtime_native.c` already had a **partial** `SPL_CORE_C_WEAK` fallback set
  (`rt_atomic_int_new/load/compare_exchange` only) mirroring `runtime.c`'s
  "Atomic handles" section (same file that cannot be linked in wholesale).
  Completed the set under the same `RtCoreAtomicInt`/`RtCoreAtomicBool` +
  `SPL_CORE_C_WEAK` convention, mirroring `runtime.c`'s exact seq_cst
  semantics. `rt_atomic_bool_fetch_and/or/not` have **zero prior C
  implementation anywhere** (`runtime.c` only ever had bool new/load/store/
  swap/compare_exchange/free) — implemented via a portable CAS-retry loop
  (GCC's generic-atomics expansion rejects `atomic_fetch_and/or_explicit`
  directly on `atomic_bool`: "operand type incompatible with argument 1 of
  `__atomic_fetch_and`"; clang accepts it, so this was caught only by
  building with both compilers). `fetch_not` reduces to `fetch_xor(true)`,
  identical to Rust's own `rt_atomic_bool_fetch_not`
  (`runtime/src/value/sffi/atomic.rs`: `atomic.fetch_xor(true, SeqCst)`).

### Verification

- **Grep count, exactly one definition per symbol** (checked all 32; sample):
  every one of the 32 fixed symbols appears exactly once as `nm
  --defined-only` output in the standalone-compiled `runtime_native.o`.
- **`cargo check --release --bin simple -j4`** (fresh `CARGO_TARGET_DIR`):
  clean — `Finished `release` profile [optimized] target(s) in 1m 02s`, 0
  errors (only 7 pre-existing warnings in `simple-compiler`, unrelated to
  this change).
- **`sh scripts/check/check-c-runtime-compiles-push.shs`**:
  `PASS — 132 file(s) compiled, 0 errors (5 skipped for unavailable external
  dependencies)`.
- **Real relink of the actual failed object set**, patching only
  `runtime_native.o` inside a copy of the real `libsimple_runtime.a`:
  undefined-symbol count went from **246 -> 214** (32 fewer), **0 new
  duplicate-symbol errors**, and `comm -23` between the before/after ground-truth
  lists shows the removed set is *exactly* the 32 symbols implemented here —
  no accidental resolution of anything else, no regression.
- **Behavioural test** (not just linkage):
  `src/runtime/test/rt_bootstrap_c_lane_atomic_math_time_selfcheck.c` —
  exercises all 32 symbols against real values/state transitions (monotonic
  strictly-increasing across a real 20ms sleep; math functions against known
  closed-form values `asin(1)=pi/2`, `log2(8)=3`, etc.; full atomic
  int/bool lifecycles including fetch-op return-value-is-previous-value
  semantics and CAS success/failure; ABI version/deferred-flag consistency).
  Built and run directly against a standalone `runtime_native.o` (same
  recipe as the pre-existing `rt_runtime_kind_probes_core_c_selfcheck.c`
  beside it): `PASS: bootstrap core-C lane atomic/math/time additions behave
  correctly`.

## Runnable check for future regressions

`scripts/check/extern-backing-census.shs` already reads DEFINED symbol
tables out of real link artifacts via `nm` (the single source of truth per
`.claude/rules/vcs.md`'s unbacked-extern-ratchet section) and classifies
`GENUINELY_MISSING` vs `DEAD_DECLARATION` vs backed. It does not currently
distinguish *per-lane* backing (a symbol backed in the Rust-hosted lane but
missing from the core-C-bootstrap lane reads as "backed" overall, which is
exactly how this 246-symbol set went undetected). Extending it to also scan
`build_core_c_runtime_library`'s member list specifically (the 25→27-member
archive under `bootstrap_mutex_core_c_runtime`, now including the 32 symbols
added here) as its own named lane, alongside the existing Rust/C-general
split, is the natural fit — filed as a follow-up rather than done in this
change, since `extern-backing-census.shs` has its own selftest contract that
a partial edit under time pressure risks regressing. Until that lands, this
census file plus the failing linker reproduction recipe in "How completeness
was established" above is the fail-closed check: rerun
`clang++ @spl_objects.rsp ... -Wl,--error-limit=0` against any future kept
failed-link object set and diff against `linker_ground_truth.txt`
(preserved alongside this doc's source data) to see instantly whether a
regression reintroduced any of the 32.

## Update 2026-09-07 (batch 2): 10 more bucket-2-misc symbols fixed

Implemented on `work/stage2-link-symbols-batch2` (separate change from the 32
above, and from the still-open #492/#493 PRs — checked both branches first to
avoid duplicating their work; see "What #492/#493 already cover" below).
Added to `src/runtime/runtime_native.c`: `rt_env_home`, `rt_env_vars`,
`rt_file_open`, `rt_file_close`, `rt_file_exists_str`, `rt_file_hash`,
`rt_file_canonicalize`, `rt_file_read_lines`, `rt_file_mmap_read_bytes`,
`rt_dir_glob` — all previously counted in the "2-deferred: Rust-only, C-lane
gap (misc)" row above (90 -> 80 remaining in that bucket).

**Two real ABI divergences found by disassembling the kept object set**
(`native-objects-8HIZif/mod_837.o`, `lib__nogc_sync_mut__sffi__fs__*`), not by
reading the Rust signature or the `codegen/runtime_sffi.rs` `RuntimeFuncSpec`
table:
- `rt_file_open`: `RuntimeFuncSpec` declares 4 `I64` params, but the real
  call only ever sets up 3 registers (path_ptr, path_len, mode), matching
  `descriptor.rs`'s actual `(path_ptr, path_len, mode: i32)` and
  `src/lib/nogc_sync_mut/sffi/fs.spl:130`'s `extern fn rt_file_open(path:
  text, mode: i32) -> i32`. Implemented with the 3-arg shape, not
  `RuntimeFuncSpec`'s 4.
- `rt_dir_glob`: `directory.rs`'s Rust fn takes FOUR args (dir_ptr, dir_len,
  pattern_ptr, pattern_len) and forwards to `rt_file_find`, but
  `src/lib/nogc_sync_mut/sffi/fs.spl:18` declares
  `extern fn rt_dir_glob(pattern: text) -> [text]` (one text arg) and the
  real call sets up exactly two words (ptr, len). Porting the 4-arg Rust body
  verbatim would have read the pattern's own (ptr,len) as a bogus
  (dir_ptr,dir_len) pair. Implemented instead as a single-pattern `glob(3)`
  call, matching the real 2-word call site.

`rt_file_exists_str` and `rt_file_hash` both tail-call with zero argument
setup (boxed `RuntimeValue` text handle passed straight through in x0), the
same single-word-boxed-text shape as the `rt_remove` ABI fix on the
#493 branch — decoded via the existing `rt_core_string_to_cpath` /
`rt_core_string_bytes` helpers.

**Explicitly NOT implemented in this batch, with reasons** (still counted in
the "2-deferred: Rust-only, C-lane gap (misc)" row, 80 remaining):
- `rt_array_sum`, `rt_array_sorted` — the Rust bodies
  (`runtime/src/value/collections.rs`) operate on the Rust-tagged
  `RuntimeArray` representation (`is_int`/`is_float`/`from_int`/`from_float`
  on a `RuntimeValue`), a different value-tagging scheme than the
  `RtCoreArray`/`RtCoreValue` representation this lane's `rt_array_new`/
  `rt_array_push`/`rt_dict_*` family already uses. A mechanical port would
  silently misread the C-side tagged values; needs the C-side decode, not a
  mirror.
- `rt_cli_handle_compile` — Rust body is `delegate_to_simple_binary("compile",
  args)`: calls into the compiler pipeline. Out of scope per task instructions.
- `rt_cli_run_tests_process_args` — Rust body calls `run_tests_with_args`,
  i.e. the test runner/compiler pipeline. Out of scope per task instructions.
- `rt_mmap` — Rust body (`file_io/file_ops.rs`) gates on
  `runtime_capability_allowed(READ_FILE_CAPABILITY_ID)` /
  `WRITE_FILE_CAPABILITY_ID`, the same capability-sandbox subsystem
  (`security_runtime.rs`) as the explicitly-excluded `rt_exec`/`rt_process_*`
  family — not a mechanical mirror.
- `rt_execute_native` — sole Rust impl is in `security_runtime.rs`, same
  capability-sandboxed family as `rt_exec`. Out of scope per task
  instructions.
- `rt_file_atomic_write_mode`, `rt_file_list_dir`, `rt_file_mode`,
  `rt_fs_read_text` — 0 C, 0 Rust *native* implementation on either side
  (confirmed unchanged from the original census). Out of scope per task
  instructions; a different problem, not invented here.

### What #492/#493 already cover (checked before starting, not re-touched)

- PR #492 (`work/stage2-bucket2-rust-only`, open): `rt_file_fsync`,
  `rt_file_lock`, `rt_file_unlock`, `rt_load_barrier`, `rt_store_barrier`, the
  full `rt_log_*` family (7), `rt_madvise`, `rt_mem_attr_enabled`,
  `rt_mem_attr_set_owner`, `rt_msync`, `rt_munmap`, `rt_path_basename`,
  `rt_path_ext`, `rt_path_separator`, `rt_progress_*` (5), `rt_random_randint`,
  `rt_random_uniform`, `rt_remove`, `rt_time_now_seconds`,
  `rt_typed_bytes_u8_data_at` (30 total).
- PR #493 (`work/stage2-simd-iofile`, open): the full `rt_io_file_*` family
  (13) and the `rt_simd_*` family (23), plus a follow-up commit fixing
  `rt_remove`'s ABI (boxed text handle, not a raw C-string pointer).

### Verification (batch 2)

- **Relink, isolating exactly this change's effect.** The kept object set's
  own `libsimple_runtime.a` member `runtime_native.o` is a stale snapshot
  (older than current `origin/main` — it predates an unrelated `rt_alloc`/
  `rt_free`/etc. addition to `runtime_native.c` that must be compiled with
  `-DSIMPLE_RUNTIME_MEMORY_OWNER=1`, matching the real build
  (`native_project/tools.rs:561`), or it duplicate-conflicts against
  `runtime_memory.o`). Correct methodology: compile `runtime_native.c` fresh
  from current `origin/main` HEAD (before this change) as the baseline,
  compile it again with this change applied, patch each into its own copy of
  the archive, and relink both against the same untouched `spl_objects.rsp` +
  capsule archive + `libunwind.so`. Before: **214** undefined symbols, 0
  duplicates. After: **204**, 0 duplicates — exactly 10 fewer.
  `comm -23 before after` = exactly the 10 symbols listed above, byte for
  byte; `comm -13 before after` = empty (no new undefined symbol appeared).
- **`cargo check --release --bin simple -j4`** (fresh `CARGO_TARGET_DIR`):
  clean, `Finished` release profile in ~1m 05s, only pre-existing warnings.
- **`sh scripts/check/check-c-runtime-compiles-push.shs`**: `PASS — 133
  file(s) compiled, 0 errors (5 skipped for unavailable external
  dependencies)`.
- **Behavioural test**:
  `src/runtime/test/rt_bootstrap_c_lane_fs_env_selfcheck.c` — 20 checks
  against real filesystem/environment state: `rt_env_home`/`rt_env_vars`
  against a just-`setenv`'d value; `rt_file_open`/`rt_file_close`/
  `rt_file_exists_str` against a real file and a real fd (including a
  double-close failure and a missing-file open returning -1);
  `rt_file_hash` against the known SHA-256("abc") test vector, plus the
  empty-not-nil failure case; `rt_file_canonicalize` popping a real ".."
  component and joining a relative path onto the real `cwd`;
  `rt_file_read_lines` splitting `\n`/`\r\n` correctly with no spurious
  trailing empty line; `rt_file_mmap_read_bytes` preserving every byte
  including `0x00`/`0xFF`; `rt_dir_glob` matching exactly the real files a
  real glob pattern should match. All 20 PASS. **Non-vacuity proved**: a copy
  of `runtime_native.c` with `rt_file_exists_str` deliberately forced to
  always `return 0` was recompiled and relinked against the same selfcheck
  harness — it failed exactly the one targeted assertion (`FAIL:
  rt_file_exists_str finds a real file`, exit 1) while every other check
  still passed, then the real implementation was restored and reverified
  green (exit 0).

## Bucket 3/4 handoff (not touched here — per task instructions)

See the table below; rows tagged `3-UFCS-dotted` and `4-lenient-unresolved-global`.
The UFCS classifier agent already working this per the task brief owns buckets 3
and 4. One item flagged for that owner beyond the bucket list itself: `raise`
resolves at real link time to libc's `raise(int)` (POSIX signal-raise) — a bare
`raise` identifier in Simple source should never silently become that call; this
is the same `lenient_unresolved_global` fallback class as `Unit`; drop-in libc
resolution is a name collision, not a fix.

## Full symbol table


### FIXED (bucket 1/2, mechanical — implemented this change, 32)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_atomic_bool_compare_exchange` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_fetch_and` | lib__nogc_sync_mut__atomic | — | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_fetch_not` | lib__nogc_sync_mut__atomic | — | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_fetch_or` | lib__nogc_sync_mut__atomic | — | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_free` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_load` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_new` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_store` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_bool_swap` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_fetch_add` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_fetch_and` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_fetch_or` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_fetch_sub` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_fetch_xor` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_free` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_store` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_atomic_int_swap` | lib__nogc_sync_mut__atomic | src/runtime/runtime.c, | src/compiler_rust/runtime/src/value/sffi/atomic.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_math_acos` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_asin` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_atan2` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_atan` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_ceil` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_cosh` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_floor` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_log10` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_log2` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_log` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_sinh` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_math_tanh` | lib__nogc_sync_mut__io__math | — | src/compiler_rust/runtime/src/value/sffi/math.rs, |
| `rt_simple_abi_version` | compiler__driver__driver_build__incremental | src/runtime/runtime.c, | — |
| `rt_simple_abi_version_deferred` | compiler__driver__driver_build__incremental | src/runtime/runtime.c, | — |
| `rt_time_monotonic_ns` | compiler__driver__cache__native_noop_admission | — | — |

### Bucket 1 candidates with no reference semantics (handed off, 15)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_file_view_close_v1` | lib__common__io__read_only_file_view | — | — |
| `rt_file_view_device_v1` | lib__common__io__file_view_buffered | — | — |
| `rt_file_view_inode_v1` | lib__common__io__file_view_buffered | — | — |
| `rt_file_view_map_copy_v1` | lib__common__io__read_only_file_view | — | — |
| `rt_file_view_mapping_supported_v1` | lib__common__io__read_only_file_view | — | — |
| `rt_file_view_open_beneath_no_follow_v1` | lib__common__io__read_only_file_view | — | — |
| `rt_file_view_pread_exact_v1` | lib__common__io__file_view_buffered | — | — |
| `rt_file_view_prefetch_v1` | lib__common__io__read_only_file_view | — | — |
| `rt_file_view_size_v1` | lib__common__io__file_view_buffered | — | — |
| `rt_native_build` | app__cli__bootstrap_main | — | — |
| `rt_pinned_archive_close_v1` | compiler__driver__cache__pinned_archive_capability | — | — |
| `rt_pinned_archive_device_v1` | compiler__driver__cache__pinned_archive_capability | — | — |
| `rt_pinned_archive_inode_v1` | compiler__driver__cache__pinned_archive_capability | — | — |
| `rt_pinned_archive_open_beneath_v1` | compiler__driver__cache__pinned_archive_capability | — | — |
| `rt_pinned_archive_size_v1` | compiler__driver__cache__pinned_archive_capability | — | — |

### Bucket 3: UFCS/method resolve-by-name (owned by the UFCS classifier agent, 7)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `Array.remove_at` | lib__scv__compile_source_inventory | — | — |
| `CompilerDriver.compile_to_vhdl` | compiler__driver__driver_aot_pipeline | — | — |
| `DynamicBackendPluginLease.admitted_handle` | compiler__backend__backend_plugin__dynamic_adapter | — | — |
| `GenericTemplate.is_err` | compiler__mono__instantiation | — | — |
| `MirBuilder.emit_comment` | compiler__mir___MirLoweringExpr__method_calls_literals | — | — |
| `str.split_whitespace` | compiler__driver__cache__dirty_module_record | — | — |
| `str.strip` | compiler__driver__driver_build__incremental | — | — |

### Bucket 4: lenient-unresolved-global (handed off, 3)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_numeric.f64` | lib__common__search__types | — | — |
| `Unit` | compiler__driver__action_graph__scc_compile_outputs | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/vulkan/sync.rs,src/compiler_rust/runtime/src/bytecode/tests.rs,src/compiler_rust/runtime/src/bytecode/vm.rs,src/compiler_rust/runtime/src/value/sffi_macros.rs,src/compiler_rust/runtime/src/value/torch/nn_activations.rs,src/compiler_rust/runtime/src/value/channels.rs,src/compiler_rust/runtime/src/value/sync.rs,src/compiler_rust/runtime/src/hir_core.rs, |
| `virtual_source_store` | compiler__common__cache_contract__virtual_source_registration_v1 | — | — |

### Bucket 2 deferred: sqlite lane wiring (deliberate exclusion + caller bug, not a runtime gap, 24)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_sqlite_begin` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_bind_float` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_bind_int` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_bind_null` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_bind_text` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_changes` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_close` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_column_count` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_column_name` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_column_text` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_commit` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_error_message` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_execute_batch` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_execute` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_finalize` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_last_insert_rowid` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_open` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_open_memory` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_prepare` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_query_done` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_query` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_query_next` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_reset` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |
| `rt_sqlite_rollback` | lib__nogc_sync_mut__io__sqlite_sffi | src/runtime/runtime_sqlite.c, | — |

### Bucket 2 deferred: cranelift JIT bridge (needs a design decision, not a mechanical port, 75)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_cranelift_aot_define_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_append_block_param` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_append_func_params` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_band` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_bconst` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_begin_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_bitcast` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_block_param` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_bnot` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_bor` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_brif` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_bxor` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_call_arg` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_call_args_clear` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_call_function_ptr` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_call_indirect` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_call` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_create_block` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_data_addr_in_func` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_declare_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_declare_global_data` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_declare_global_data_v2` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_declare_string_data` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_define_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_emit_object_raw` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_end_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fadd` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fcmp` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fconst` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fcvt_from_sint` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fcvt_from_uint` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fcvt_to_sint` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fcvt_to_uint` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fdemote` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fdiv` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_finalize_module` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fmul` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fpromote` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_free_module` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_fsub` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_function_addr_in_func` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_get_function_ptr` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_iadd` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_icmp` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_iconst` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_import_function` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_imul` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_ireduce` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_ishl` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_isub` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_jump` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_load` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_new_aot_module_triple` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_new_module` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_new_signature` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_null` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_return` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_return_void` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_sdiv` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_seal_all_blocks` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_seal_block` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_sextend` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_sig_add_param` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_sig_set_return` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_srem` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_sshr` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_stack_addr` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_stack_slot` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_store` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_switch_to_block` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_trap` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_udiv` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_uextend` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_urem` | lib__nogc_sync_mut__sffi__codegen | — | — |
| `rt_cranelift_ushr` | lib__nogc_sync_mut__sffi__codegen | — | — |

### Bucket 2 deferred: Rust-only, core-C-bootstrap lane gap (real debt, too large to safely port in this change, 90)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_array_sorted` | compiler__driver__action_graph__build_action_v1 | — | src/compiler_rust/runtime/src/value/collection_tests.rs,src/compiler_rust/runtime/src/value/collections.rs, |
| `rt_array_sum` | compiler__backend__backend__llvm_type_mapper | — | src/compiler_rust/runtime/src/value/collection_tests.rs,src/compiler_rust/runtime/src/value/collections.rs, |
| `rt_cli_handle_compile` | app__io__cli_ops | — | src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_cli_run_tests_process_args` | app__io__cli_ops | — | src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_dir_glob` | lib__nogc_sync_mut__sffi__fs | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/sffi/file_io/directory.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_env_home` | lib__nogc_async_mut__env__platform | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/sffi/env_process.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_env_vars` | lib__nogc_async_mut__env__variables | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/sffi/env_process.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_exec` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_execute_native` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/security_runtime.rs, |
| `rt_file_atomic_write_mode` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_canonicalize` | lib__nogc_sync_mut__sffi__fs | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_close` | lib__nogc_sync_mut__sffi__dynamic | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_exists_str` | lib__nogc_sync_mut__sffi__fs | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/cli_sffi.rs, |
| `rt_file_fsync` | compiler__driver__action_graph__persisted_graph | src/runtime/runtime.c, | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_hash` | lib__nogc_sync_mut__sffi__io | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/cli_sffi.rs, |
| `rt_file_list_dir` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_lock` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_mmap_read_bytes` | lib__nogc_sync_mut__io__file_ops | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_mode` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_open` | lib__nogc_sync_mut__sffi__fs | src/runtime/runtime_native.c,; FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_read_lines` | lib__nogc_sync_mut__sffi__io | FIXED batch 2 (src/runtime/runtime_native.c) | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_unlock` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_fs_read_text` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_get_host_target_code` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs, |
| `rt_io_file_delete` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_exists` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_flush` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_created` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_flags` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_modified` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_size` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_read` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_read_line` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_seek` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_set_permissions` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_write_all` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_write` | lib__nogc_sync_mut__io__file | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_load_barrier` | lib__nogc_sync_mut__io__volatile_ops | — | src/compiler_rust/runtime/src/lib.rs, |
| `rt_log_clear_scope_levels` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_emit` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_get_global_level` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_get_scope_level` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_is_enabled` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_set_global_level` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_log_set_scope_level` | app__io__mod | — | src/compiler_rust/runtime/src/value/log_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_madvise` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_mem_attr_enabled` | lib__nogc_sync_mut__sffi__platform | — | src/compiler_rust/runtime/src/value/heap.rs, |
| `rt_mem_attr_set_owner` | lib__nogc_sync_mut__sffi__platform | — | src/compiler_rust/runtime/src/value/heap.rs,src/compiler_rust/runtime/src/value/sffi/contracts.rs,src/compiler_rust/runtime/src/value/profiler_sffi.rs, |
| `rt_mmap` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_msync` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_munmap` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_path_basename` | lib__nogc_sync_mut__sffi__io | — | src/compiler_rust/runtime/src/value/sffi/file_io/path.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_path_ext` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/path.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_path_separator` | compiler__common__cache__phase_compatibility_path_io | — | src/compiler_rust/runtime/src/value/sffi/file_io/path.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_process_run_with_limits` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs, |
| `rt_process_spawn_inherit` | app__io__process_ops | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_progress_clock_now_nanos` | lib__common__time_utils | src/runtime/runtime_timestamp.c, | src/compiler_rust/runtime/src/value/sffi/time.rs, |
| `rt_progress_tls_clear` | lib__common__time_utils | src/runtime/runtime_timestamp.c, | src/compiler_rust/runtime/src/value/sffi/time.rs, |
| `rt_progress_tls_is_initialized` | lib__common__time_utils | src/runtime/runtime_timestamp.c, | src/compiler_rust/runtime/src/value/sffi/time.rs, |
| `rt_progress_tls_start_nanos` | lib__common__time_utils | src/runtime/runtime_timestamp.c, | src/compiler_rust/runtime/src/value/sffi/time.rs, |
| `rt_progress_tls_store_start_nanos` | lib__common__time_utils | src/runtime/runtime_timestamp.c, | src/compiler_rust/runtime/src/value/sffi/time.rs, |
| `rt_random_randint` | app__io__mod | — | src/compiler_rust/runtime/src/value/sffi/random.rs, |
| `rt_random_uniform` | app__io__mod | — | src/compiler_rust/runtime/src/value/sffi/random.rs, |
| `rt_remove` | lib__nogc_async_mut__io__file | src/runtime/runtime.c,src/runtime/runtime_hosted_fs.c, | src/compiler_rust/runtime/src/value/collections.rs, |
| `rt_simd_add_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_add_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_add_u8x16` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_byte_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_aes_round_last_u8x16` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_aes_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_aes_round_u8x16` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_aes_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_and_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_and_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_clmul_hi_u64` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_clmul_lo_u64` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_mul_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_mul_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_or_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_or_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shl_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shl_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shr_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shr_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_sub_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_sub_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_i32x4` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_i32x8` | lib__nogc_sync_mut__simd | — | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_u64x2` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_u8x16` | lib__nogc_sync_mut__simd_crypto | — | src/compiler_rust/runtime/src/value/simd_byte_ops.rs, |
| `rt_store_barrier` | lib__nogc_sync_mut__io__volatile_ops | — | src/compiler_rust/runtime/src/lib.rs, |
| `rt_time_now_seconds` | lib__nogc_sync_mut__io__time_ops | src/runtime/runtime.c,src/runtime/runtime_time.c, | src/compiler_rust/runtime/src/value/sffi/time.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_typed_bytes_u8_data_at` | lib__common__crypto__sha256 | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/collections.rs,src/compiler_rust/runtime/src/value/mod.rs, |
