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

### Direct header-manifest warm-hit lookup (follow-up closing Residual cost #1)

`runtime_object_cache_windows.spl` now implements direct mode ahead of `-E` and
`-###` so warm builds skip all 45 serial preprocessor and driver-plan spawns:

- `runtime_windows_extract_linemarker_headers_v1`: parses `# <line> "<path>"`
  (and `#line <line> "<path>"`) linemarkers from `.i` text, unescaping/normalizing
  `\\` and `\` to `/`, deduplicating in order, and ignoring synthetic markers
  such as `<built-in>`, `<command line>`, `<command-line>`, and `<scratch space>`.
- `runtime_windows_direct_manifest_key_v1`: computes a 64-hex direct manifest
  key from `(toolchain_id, compiler_flags, normalized_source_path)` (including
  `compiler_digest`, runtime `context`, output-normalized flags, and compiler
  env vars in `runtime_windows_cached_compile_with_runner_v1`).
- `<cache_root>/keys/<direct_key>.deps.sdn`: canonical SDN (`simple-windows-rt-direct-v1`,
  helpers `runtime_windows_direct_manifest_roundtrip` and
  `runtime_windows_direct_manifest_publish_v1`) recording `content_key` and
  each dependency `(normalized_path, sha256)` ONLY when every listed file
  passes `file_is_regular_no_follow` and hashes cleanly. Published on
  `runtime_windows_cache_publish_batch_v1` (after batch-wide toolchain
  recheck and dependency SHA-256 re-verification) or refreshed on fallback `-E`
  content-cache hit.
- `runtime_windows_direct_manifest_lookup_v1`: runs before creating any
  `runtime-tu-*` staging dir or invoking `-E` / `-###` in
  `runtime_windows_cached_compile_with_runner_v1` (with `runtime_windows_cached_compile_v1`
  delegating via `process_run`). Verifies `<direct_key>.deps.sdn`, presence of
  `keys/<content_key>`, current regular-file SHA-256 of every recorded
  dependency, and `runtime_object_cache_lookup_v1`; on full match returns the
  cached `.o` immediately (`Windows direct header cache hit`). Any missing,
  non-regular, or modified header/source, corrupt manifest, or evicted `.o`
  falls back cleanly to `-E` and refreshes `<direct_key>.deps.sdn`.

## Evidence

- Spec: `test/01_unit/compiler/backend/runtime_object_cache_windows_gnu_spec.spl`:
  - Prior fix failed 4/4 before and passed 4/4 after.
  - Extended to 8/8 passing (`simple.exe test ... --mode=interpreter` at
    `5911a32cab0c3f0c7bf6440a377e7263487c028e`), covering linemarker extraction
    and normalization, direct key determinism/invalidation, `.deps.sdn` roundtrip,
    fail-closed refusal on missing/directory dependencies, end-to-end callback
    verification (cold miss -> `.deps.sdn` publish -> warm direct hit with 0
    preprocess/plan/compile invocations -> macro header mutation invalidation &
    refresh -> comment-only header mutation invalidation with content-cache hit
    & `.deps.sdn` refresh -> corrupt manifest / missing header / swept `.o`
    fallback), while `runtime_object_cache_material_spec.spl` (6/6) and
    `runtime_object_cache_io_spec.spl` (3/3) continue to pass.
- Nil check: `sh scripts/check/check-nil-outside-unsafe-added.shs --rank`
  reports `0` on `runtime_object_cache_windows.spl` (down from `1`) and `0` on
  `runtime_object_cache_windows_gnu_spec.spl`.
- Real adapter, seed interpreter, llvm-mingw `clang.exe`, `runtime_memtrack.c`:
  - toolchain identity is non-empty;
  - the miss returns exit 0 with a key, and publish returns true;
  - the second call prints `Windows content cache hit` with no pending key;
  - the key is identical across two separate processes.
- Shell emulation over the exact 45-TU set (43 present, same flags, host under
  load from a concurrent bootstrap): miss 79.7 s total, hit (`-E` + `-###`)
  42.6 s total. With direct header-manifest warm-hit lookup skipping `-E` and
  `-###`, warm runtime-object lookup removes that ~42.6 s serial preprocess/plan
  cost (pending native verification after compiler redeploy).
- The `-###` plan for a GNU `.i` compile selects `cpp-output` and contains none
  of the refused external-input flags.

## Residual costs (open)

1. Warm-hit serial `-E` + `-###` (~0.5 s/TU, ~42.6 s total) is now eliminated by
   direct header-manifest lookup above; cold misses remain serial (follow-up:
   parallel TU loop if cold miss time becomes a bottleneck).
2. A miss now costs `-E` + 2 x `-###` + compile. It happens only when
   `src/runtime` or the toolchain changes, and the prime step absorbs it.
3. About 70 s before the parse closure for a 1-module program, not yet attributed.
   Trace it with `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1` and
   `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_SCAN_PHASES=1`.
4. `phase3:cold_receipts` takes about 9 s for one module.
5. Together, items 3 and 4 still contribute to time before the first `.o` on cold
   builds (measured ~105 s before direct mode; warm re-measure pending native redeploy).

## Verification (pending, native)

Deploy a compiler that contains this change. Then run two warm p2_add builds with
`SIMPLE_COMPILER_TRACE=1` and `SIMPLE_RT_OBJ_CACHE_DIR=<dir>`. The second build
must print 45 `Windows direct header cache hit` lines (zero `-E` / `-###`
spawns for unchanged headers). Compare the gap from `.o` to the link command
(about 92 s before the fix, ~42.6 s with `-E`/`-###` hit, near-zero hash check
with direct mode).
