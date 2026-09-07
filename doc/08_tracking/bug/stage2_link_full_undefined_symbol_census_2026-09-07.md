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
| FIXED (1/2, mechanical) | 32 | Implemented in the first change — see below |
| FIXED (2, `rt_simd_*` + `rt_io_file_*`) | 36 | Implemented in this follow-up change — see "What was implemented (rt_simd_* / rt_io_file_*, this change)" below. 23 `rt_simd_*` (not 22 as originally scoped — the family has 23 rows in the full symbol table below) + 13 `rt_io_file_*` (not 12 — `rt_io_file_exists`/`rt_io_file_delete` take a path, not an fd, but are part of the same census row group). |
| 1-candidate, no reference semantics | 15 | `rt_file_view_*_v1` (9), `rt_pinned_archive_*_v1` (5), `rt_native_build` (1) — 0 C, 0 Rust *native* symbol, and no header/doc contract exists to mirror. Handed off. |
| 2-deferred: cranelift JIT bridge | 75 | `rt_cranelift_*` — implemented in Rust (`codegen/cranelift_sffi.rs`, `interpreter_extern/cranelift.rs`) for the seed's own JIT; this archive is a plain native-AOT C lane with no JIT concept. Handed off — needs a design decision (stub vs. exclude the JIT-only call sites from this closure), not a mechanical port. |
| 2-deferred: sqlite lane wiring | 24 | `rt_sqlite_*` — **deliberately excluded** from the core-C archive by design (`build_sqlite_runtime_object`'s doc comment in `native_project/tools.rs`: avoids forcing `-lsqlite3` on every native binary). The real bug is the caller not detecting sqlite usage and adding the on-demand object + `-lsqlite3` for *this* closure. Lane-wiring bug, not a runtime gap. Handed off. |
| 2-deferred: Rust-only, C-lane gap (misc, remaining) | 54 | Implemented in Rust (`runtime/src/value/**`, mostly `#[no_mangle] extern "C" fn`) but never ported to the core-C-bootstrap archive: `rt_file_*` (fd/path helpers distinct from the now-fixed `rt_io_file_*` family), `rt_log_*`, `rt_random_*`, `rt_path_*`, `rt_env_*`, `rt_process_*`, `rt_dir_glob`, `rt_exec`, `rt_execute_native`, `rt_fs_read_text`, `rt_get_host_target_code`, `rt_array_sum`/`rt_array_sorted`, `rt_cli_handle_compile`/`rt_cli_run_tests_process_args`, `rt_mem_attr_*`, `rt_typed_bytes_u8_data_at`. **The `rt_simd_*` (23) and `rt_io_file_*` (13) rows that were previously counted in this bucket (90 total) are now FIXED — see the row above.** `rt_exec`/`rt_process_*`/`rt_get_host_target_code` need `security_runtime.rs`'s sandbox subsystem, not a mechanical port — explicitly out of scope for the mechanical-port pass. `rt_file_atomic_write_mode`, `rt_file_list_dir`, `rt_file_mode`, `rt_fs_read_text` have **no implementation on either side** (0 C, 0 Rust) — a different problem, left alone. Handed off with this census as the punch list. |
| 3: UFCS/method resolve-by-name | 7 | `Array.remove_at`, `CompilerDriver.compile_to_vhdl`, `DynamicBackendPluginLease.admitted_handle`, `GenericTemplate.is_err`, `MirBuilder.emit_comment`, `str.split_whitespace`, `str.strip`. Owned by the UFCS classifier agent already working this per the task's instructions — not touched here. |
| 4: lenient-unresolved-global | 3 | `Unit`, `virtual_source_store`, `rt_numeric.f64` — same `lenient_types` HIR-fallback mechanism as `Unit`'s documented `note:` block. |

Table counts: 32+36+15+75+24+54+7+3 = 246, matching the linker's own count exactly
(re-split 2026-09-07 continued: the original 90-row "Rust-only, C-lane gap (misc)"
bucket split into 36 now-FIXED `rt_simd_*`/`rt_io_file_*` rows + 54 still-deferred
rows; 32+90=122 before this change, 32+36=68 fixed total after it).

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

## What was implemented (rt_simd_* / rt_io_file_*, this follow-up change)

Two named families from the "2-deferred: Rust-only, C-lane gap (misc)" bucket,
36 symbols total (all added to `src/runtime/runtime_simd_dispatch.c` and
`src/runtime/runtime_native.c`, both already archive members of
`bootstrap_mutex_core_c_runtime`/`build_core_c_runtime_library` — no new file,
no whitelist change).

### `rt_simd_*` (23 symbols: `add/sub/mul/xor/and/or/shl/shr` over i32x4 and
i32x8, `add`/`xor` over u8x16, `aes_round_u8x16`/`aes_round_last_u8x16`,
`clmul_lo_u64`/`clmul_hi_u64`/`xor_u64x2`)

**The Rust `pub extern "C" fn rt_simd_*` signatures in `simd_int_ops.rs` /
`simd_byte_ops.rs` (a scalar-lane-array ABI: e.g. `rt_simd_add_i32x4(a0..a3,
b0..b3, out: *mut i32)`) are NOT the real ABI and were not mirrored — their
own doc comments admit they are provisional ("once a Vec4i marshalling layer
lands they will receive the actual lane data"), and neither family is
registered in `codegen/runtime_sffi.rs`'s `RUNTIME_FUNCS`, so nothing enforces
that shape at a call site.** The real ABI was determined by disassembling the
actual generated call sites in the kept failed-link object set
(`native-objects-8HIZif/mod_842.o` for i32x4/i32x8, `mod_843.o` for
u8x16/u64x2): every `lib__nogc_sync_mut__simd__simd_*` wrapper tail-calls its
`rt_simd_*` counterpart with plain `int64_t` args/return, each a tagged
pointer (`payload | 1`) to a flat array of `int64_t` lane slots allocated via
`rt_alloc` — identical to the convention this file already used for
`rt_simd_add_f32x4`/`rt_simd_add_u32x4`/etc. (see the block comment at
`runtime_simd_dispatch.c` line ~2246, itself reverse-engineered from
`mod_814.o`/`mod_815.o` by an earlier pass on the Windows LNK2019 inventory).
`rt_simd_aes_round_u8x16`/`rt_simd_aes_round_last_u8x16` additionally cross-
checked clean against their *already-registered* `RUNTIME_FUNCS` spec
(`&[I64, I64] -> &[I64]`, `runtime_sffi.rs:594-595`). No codegen change was
needed or made — the existing generic struct-boxing path already produces the
correct calls; only the missing C-side symbols were added, reusing the file's
existing `rt_simd_vec_payload`/`rt_simd_lane_u64`/`rt_simd_result_vec` helpers.

Semantics were mirrored from the Rust lane kernels (`simd_int_ops.rs`,
`simd_byte_ops.rs`, `simd_aes_ops.rs`, `simd_clmul_ops.rs`), not guessed:
32-bit wrapping add/sub/mul, bitwise xor/and/or, LOGICAL (zero-fill) shl/shr
with the shift count masked to `0..31`; per-lane wrapping u8 add with no
cross-lane carry; AES round = `MixColumns(SubBytes(ShiftRows(state))) XOR
key` (last round skips MixColumns), FIPS 197 SBOX/ShiftRows/MixColumns copied
byte-for-byte from the Rust scalar fallback (and cross-checked against the
Rust file's own FIPS 197 Appendix B unit test vector); carryless 64×64→128
multiply via the identical shift-and-XOR loop, `clmul_lo_u64`/`clmul_hi_u64`
operating on `Vec2u64`'s `(lo, hi)` field order per
`src/lib/nogc_sync_mut/simd_crypto.spl`.

### `rt_io_file_*` (13 symbols: `read`, `read_line`, `write`, `write_all`,
`seek`, `flush`, `set_permissions`, `meta_size`, `meta_flags`,
`meta_modified`, `meta_created`, `exists`, `delete`)

Mirrors `runtime/src/value/sffi/file_io/io_file.rs` exactly (fd validity,
mode/whence encodings, EINTR-retry-then-propagate read/write semantics,
`read_line`'s byte-at-a-time EOF-exact-positioning contract and its
discard-everything-on-error behavior, `set_permissions`'s Unix
`chmod a-w`/`chmod u+w` — not "restore previous mode" — semantics,
`meta_created`'s "0 if birth time unsupported" fallback). Reused this file's
existing `rt_text_arg_to_path`/`rt_core_nil`/`rt_byte_array_new_len`/
`rt_core_array_ptr` helpers, the same ones `rt_io_file_open`/`_close`/
`_read_all` (already resolved, immediately above) use. `rt_io_file_exists`
and `rt_io_file_delete` are the only two of the 13 that take a `text` (path)
rather than an `fd`; both were **already** registered in the seed's
`(ptr,len)` text-ABI tables (`codegen/instr/calls.rs:2603`,
`codegen/runtime_sffi.rs:2101-2102`) before this change — confirmed by
symbol-grep, not assumed — so no codegen change was needed there either. The
other 11 take only plain scalars/pointers (`fd: i64`, `data_ptr: *const u8,
data_len: u64`), the ordinary SysV calling convention with no struct-boxing
involved; the real call sites (`FileHandle.write`/`write_all` in
`mod_810.o`/`mod_837.o`) were disassembled to confirm the 3-register
`(fd, ptr, len)` shape arrives unmarshalled, which is what let this land
without touching `text_arg_indices` at all.

### Verification

- **Grep/nm count, exactly one definition per symbol**: all 23 `rt_simd_*`
  and all 13 `rt_io_file_*` symbols appear exactly once each in
  `nm --defined-only` output on the standalone-compiled `.o`s.
- **`cargo check --release --bin simple -j4`** (fresh
  `CARGO_TARGET_DIR=$HOME/.cargo-target-simd`): clean, `Finished` in ~1m —
  no Rust source was touched by this change.
- **`sh scripts/check/check-c-runtime-compiles-push.shs`**:
  `PASS — 132 file(s) compiled, 0 errors (5 skipped for unavailable external
  dependencies)`.
- **Real relink of the actual failed object set**, patching only
  `runtime_native.o`/`runtime_simd_dispatch.o` inside a copy of the real
  `libsimple_runtime.a`. A clean A/B was required to isolate this change's
  effect from other concurrent landings already present at `HEAD` (the raw
  frozen-archive baseline is 246 undefined as expected, but `HEAD` *without*
  this change already resolves 32 of them via the earlier merged fix, and
  hits 16 unrelated `duplicate symbol` errors — `rt_alloc`/`rt_free`/
  `rt_memcpy`/etc. now defined in both `runtime_native.c` and the frozen
  snapshot's untouched `runtime_memory.o`, pure version skew from mixing a
  fresh compile against a historical object snapshot, worked around for
  measurement only with `-Wl,--allow-multiple-definition`, not shipped):
  pre-this-change 214 undefined → post-this-change **178 undefined, exactly
  36 fewer**, **0 new duplicate-symbol errors introduced by this change**, and
  `comm -23` between the pre/post undefined-symbol lists is **byte-identical**
  to the 36 symbols implemented here (verified both directions: `comm -13`
  reports 0, i.e. nothing new became undefined and nothing outside this set
  was incidentally resolved).
- **Behavioural test** (not just linkage):
  `src/runtime/test/rt_bootstrap_c_lane_simd_iofile_selfcheck.c` — real
  values and state transitions, not just "the call returns": i32x4/i32x8
  signed wrapping arithmetic including an `INT32_MAX + 1 → INT32_MIN`
  wraparound case, bitwise ops, logical-vs-arithmetic shift discrimination
  (`shr(-1, 4)` must equal `0x0FFFFFFF`, must NOT equal `-1`) and shift-count
  masking (`shl(x, 33) == shl(x, 1)`); u8x16 per-lane wrap-without-carry;
  AES round against the FIPS 197 Appendix B known-answer vector (same vector
  as the Rust unit test); carryless multiply against a hand-computed GF(2)
  product including a carry-producing case; `xor_u64x2` lane-wise XOR; and a
  real fd-based file round trip (open/write_all/flush/meta_size/meta_flags/
  set_permissions toggling the readonly bit both ways/seek SEEK_SET+CUR+END/
  a read-only-fd write correctly failing with -1 rather than a fabricated
  success/read returning exactly the bytes on disk/exists/delete). Confirmed
  non-vacuous by deliberately breaking one assertion and re-running: the
  harness correctly reports `FAIL` and exit 1. Run: `PASS: bootstrap core-C
  lane rt_simd_*/rt_io_file_* additions behave correctly`.

### What remains in this bucket (handed off)

54 symbols: `rt_file_*` (the sibling fd/path family, distinct from
`rt_io_file_*`), `rt_log_*`, `rt_random_*`, `rt_path_*`, `rt_env_*`,
`rt_dir_glob`, `rt_array_sum`/`rt_array_sorted`, `rt_cli_handle_compile`/
`rt_cli_run_tests_process_args`, `rt_mem_attr_*`, `rt_typed_bytes_u8_data_at`,
plus the capability-sandboxed group (`rt_exec`, `rt_execute_native`,
`rt_process_run_with_limits`, `rt_process_spawn_inherit`,
`rt_get_host_target_code` — need `security_runtime.rs`'s sandbox subsystem,
not a mechanical port) and the four symbols with no implementation on either
side (`rt_file_atomic_write_mode`, `rt_file_list_dir`, `rt_file_mode`,
`rt_fs_read_text`).

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

### Bucket 2 deferred: Rust-only, core-C-bootstrap lane gap (real debt, remaining after this change, 54)

| Symbol | Declared/referenced (.spl callsite module) | C impl found | Rust impl found |
|---|---|---|---|
| `rt_array_sorted` | compiler__driver__action_graph__build_action_v1 | — | src/compiler_rust/runtime/src/value/collection_tests.rs,src/compiler_rust/runtime/src/value/collections.rs, |
| `rt_array_sum` | compiler__backend__backend__llvm_type_mapper | — | src/compiler_rust/runtime/src/value/collection_tests.rs,src/compiler_rust/runtime/src/value/collections.rs, |
| `rt_cli_handle_compile` | app__io__cli_ops | — | src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_cli_run_tests_process_args` | app__io__cli_ops | — | src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_dir_glob` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/sffi/file_io/directory.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_env_home` | lib__nogc_async_mut__env__platform | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_env_vars` | lib__nogc_async_mut__env__variables | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_exec` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/cli_sffi.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_execute_native` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/security_runtime.rs, |
| `rt_file_atomic_write_mode` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_canonicalize` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_close` | lib__nogc_sync_mut__sffi__dynamic | — | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_exists_str` | lib__nogc_sync_mut__sffi__fs | — | src/compiler_rust/runtime/src/value/cli_sffi.rs, |
| `rt_file_fsync` | compiler__driver__action_graph__persisted_graph | src/runtime/runtime.c, | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_hash` | lib__nogc_sync_mut__sffi__io | — | src/compiler_rust/runtime/src/value/cli_sffi.rs, |
| `rt_file_list_dir` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_lock` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_mmap_read_bytes` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_mode` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_file_open` | lib__nogc_sync_mut__sffi__fs | src/runtime/runtime_native.c, | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_read_lines` | lib__nogc_sync_mut__sffi__io | — | src/compiler_rust/runtime/src/security_runtime.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_file_unlock` | lib__nogc_sync_mut__io__file_ops | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs,src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_fs_read_text` | lib__nogc_sync_mut__sffi__fs | — | — |
| `rt_get_host_target_code` | lib__nogc_sync_mut__sffi__system | — | src/compiler_rust/runtime/src/value/sffi/env_process.rs, |
| `rt_io_file_delete` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_exists` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_flush` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_created` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_flags` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_modified` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_meta_size` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_read` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_read_line` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_seek` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_set_permissions` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_write_all` | lib__nogc_sync_mut__sffi__fs | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
| `rt_io_file_write` | lib__nogc_sync_mut__io__file | **FIXED 2026-09-07 (runtime_native.c)** | src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs, |
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
| `rt_simd_add_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_add_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_add_u8x16` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_byte_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_aes_round_last_u8x16` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_aes_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_aes_round_u8x16` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_aes_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_and_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_and_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_clmul_hi_u64` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_clmul_lo_u64` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_mul_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_mul_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_or_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_or_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shl_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shl_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shr_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_shr_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_sub_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_sub_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_i32x4` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_i32x8` | lib__nogc_sync_mut__simd | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_int_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_u64x2` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_clmul_ops.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_simd_xor_u8x16` | lib__nogc_sync_mut__simd_crypto | **FIXED 2026-09-07 (runtime_simd_dispatch.c)** | src/compiler_rust/runtime/src/value/simd_byte_ops.rs, |
| `rt_store_barrier` | lib__nogc_sync_mut__io__volatile_ops | — | src/compiler_rust/runtime/src/lib.rs, |
| `rt_time_now_seconds` | lib__nogc_sync_mut__io__time_ops | src/runtime/runtime.c,src/runtime/runtime_time.c, | src/compiler_rust/runtime/src/value/sffi/time.rs,src/compiler_rust/runtime/src/value/mod.rs, |
| `rt_typed_bytes_u8_data_at` | lib__common__crypto__sha256 | — | src/compiler_rust/runtime/src/lib.rs,src/compiler_rust/runtime/src/value/collections.rs,src/compiler_rust/runtime/src/value/mod.rs, |
