# Windows llvm-mingw runtime C objects were never cached

Status: fix-implemented-verification-pending (native "after" needs a redeployed
compiler; see Verification).

## Symptom

The Windows Stage 2 sanity probe native-builds `src/compiler/bootstrap_admission/p2_add.spl`
under `COMPILER_BUILD_TIMEOUT_SECONDS=180`. It took 266 s (caret-native log), 200 s warm,
and 436 s cold (unprimed SCV) when re-measured 2026-11-16 on the same candidate.

## Phase breakdown (warm, 200 s, cranelift, whole-program, 3 HIR threads admitted)

Taken from file mtimes plus `SIMPLE_COMPILER_PHASE_PROFILE_FILE` monotonic_ms:

| window | seconds |
|---|---|
| start -> parse-closure `selection.v1` | ~70 |
| in-process compile (session to native session open; `cold_receipts` alone ~9 s) | ~20 |
| -> `aot-*.o` written | ~8 |
| `.o` -> link command written: **runtime C compile, 45 TUs, serial, uncached** | **~92** |
| link (clang/lld) | ~2.5 |

Peak compiler RSS was 488 MiB (`rss_kib` in phase.txt).

**The HIR memory clamp is not the cause.** The closure is a single module
(`selected=1`). With `SIMPLE_HIR_SHARD_WORKER_KB=3000000` the clamp admitted
3 threads, and the build was no faster. In the original log the worker was priced
at 27262976 kB (26 GiB, from host `worker_mem_mib`), not 3 GB.

## Root cause

`runtime_compiler.spl` had two runtime-object caches. Neither covered the default
Windows toolchain, llvm-mingw `clang.exe`:

- the POSIX memo `_runtime_object_cache_dir` returns `""` when `_is_windows()`;
- the content-addressed Windows adapter ran only when `use_msvc`. Its toolchain
  identity accepted only `clang-cl.exe`.

So every Windows GNU-lane native-build recompiled the whole runtime bundle.

## Fix

`runtime_object_cache_windows.spl` now recognizes the GNU clang driver
(`runtime_windows_cache_driver_kind_v1`: `clang.exe` or `<triple>-clang.exe`)
and splits its arguments the GNU way (`runtime_windows_cache_split_args_v1`):

- preprocess: drop `-c` and `-o <obj>`, add `-E -o <stage>/input.i`;
- compile: compile that `.i`;
- key options: `-o <runtime-object>`.

For the GNU kind, the toolchain identity also hashes the adjacent `clang*.exe`.
The llvm-mingw `clang.exe` is a 14 KB wrapper that execs `clang-<N>.exe`.

`runtime_compiler.spl` enables the adapter on every Windows driver. The design is
the same preprocessed-bytes keying as the 2026-10-05 record. Stage 2 sanity
already forwards `SIMPLE_RT_OBJ_CACHE_DIR=<stage2 cache>/rt-obj`
(`bootstrap-from-scratch.sh`), so `scv_prime` fills the cache and the bounded
p2_add probe hits it.

## Evidence

- Spec: `test/01_unit/compiler/backend/runtime_object_cache_windows_gnu_spec.spl`.
  It failed 4/4 before the fix and passes 4/4 after. The existing material spec
  (6/6) and IO spec (3/3) still pass.
- Real adapter, seed interpreter, llvm-mingw `clang.exe`, `runtime_memtrack.c`:
  - toolchain identity is non-empty;
  - the miss returns exit 0 with a key, and publish returns true;
  - the second call prints `Windows content cache hit` with no pending key;
  - the key is identical across two separate processes.
- Shell emulation over the exact 45-TU set (43 present, same flags, host under
  load from a concurrent bootstrap): miss 79.7 s total, hit (`-E` + `-###`)
  42.6 s total. Projected warm probe is about 200 - 92 + ~40 ≈ 150-160 s against
  the 180 s budget. That still leaves little margin.
- The `-###` plan for a GNU `.i` compile selects `cpp-output` and contains none
  of the refused external-input flags.

## Residual costs (open)

1. The hit path is still serial and costs about 0.5 s per TU (`-E` about 0.37 s,
   `-###` about 0.17 s). Two follow-ups would remove most of it: direct mode
   (key on the headers listed in the `.i` line markers and skip `-E` when they
   are unchanged), or a parallel TU loop.
2. A miss now costs `-E` + 2 x `-###` + compile. It happens only when
   `src/runtime` or the toolchain changes, and the prime step absorbs it.
3. About 70 s before the parse closure for a 1-module program, not yet attributed.
   Trace it with `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1` and
   `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_SCAN_PHASES=1`.
4. `phase3:cold_receipts` takes about 9 s for one module.
5. Together, items 1, 3 and 4 violate the first-object-within-10 s rule. The first
   `.o` appears about 105 s after start.

## Verification (pending, native)

Deploy a compiler that contains this change. Then run two warm p2_add builds with
`SIMPLE_COMPILER_TRACE=1` and `SIMPLE_RT_OBJ_CACHE_DIR=<dir>`. The second build
must print 45 `Windows content cache hit` lines. Compare the gap from `.o` to the
link command (about 92 s before the fix).
