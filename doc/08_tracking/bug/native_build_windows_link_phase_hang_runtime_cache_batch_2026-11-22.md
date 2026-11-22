# Windows native-build "link phase hang": serial runtime C build, cache published only at batch end

Status: verification-pending (fix is spec-verified; the native "after" needs a
compiler rebuilt from this source).

Related: `unit_range_cast_native_execution_blocked_2026-11-19.md` (lanes 3/4
reported this as "link phase hangs before spawning any linker"),
`windows_gnu_clang_runtime_objects_uncached_2026-11-16.md` (the cache itself).

## Symptom

The pure-Simple compiler (`ctorfix-20261121/build/nb/cli_main.exe`, the same
bytes as `C:/dev/wt/rbnat4/build/rbnat4/cli_main.exe`) native-builds a
hello-world through codegen in ~35-70 s, then prints
`[build] phase=link state=running ...` and nothing else until the lane
timeout (600 / 900 / 1200 / 1500 s). No `.exe` and no `.tmp` output appear.

## Root cause (measured 2026-11-22, Windows 11, shared host)

It is not a deadlock. The wait/pump path, stdout/stderr draining and the
timeout-0 capture call were all ruled out:

- Process sampling during the "hang" (200 ms `Win32_Process` polls by parent
  PID) shows cli_main spawning clang about 3 times per runtime TU: `-###`
  plan, `-E` preprocess, `-c` compile. Each sample names a different
  `src/runtime/*.c`. Two lldb attach samples just caught thread 1 inside
  `CreateProcessW -> NtCreateUserProcess` between spawns.
- Before the final link, `compile_runtime_objects` (`runtime_compiler.spl`)
  compiles 45 runtime sources. On Windows with the object cache enabled
  (`windows_toolchain != ""`) this path is **serial**: `rt_parallel_eligible`
  excludes it.
- `runtime_windows_cache_publish_batch_v1` ran only **after the whole loop**.
  A cold run takes 959 s (Program Files LLVM) or 889 s (llvm-mingw) end to end
  on this host. Any lane killed before the loop finished published nothing, so
  every retry started cold again: the build never made progress.
- Warm evidence: after one complete run, the same command hit the cache 48
  times and finished in 263 s.

## Second defect found on the way (environment / selection)

Without `SIMPLE_LLVM_MINGW_ROOT` or `SIMPLE_LLVM_BIN`, `_find_c_compiler_windows`
falls through to `where clang` and picks `C:\Program Files\LLVM\bin\clang.exe`
(MSVC-flavoured LLVM). It passes `_cc_verify_compiles`, then the GNU link fails:
`ld.lld: could not open ...\lib\clang\23\lib\x86_64-w64-windows-gnu\libclang_rt.builtins.a`.
With `SIMPLE_LLVM_MINGW_ROOT=C:/Users/user/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64`,
hello-world links and runs (`hello`, rc=0). This change does not touch it.
Lanes must export that variable. Probing the default install dir before PATH
is a separate follow-up.

**Follow-up fixed (2026-11-22, work/tc1-20261122, verification-pending):**
`_find_c_compiler_windows` (GNU lane) now probes
`~/.simple/toolchains/llvm-mingw-*-ucrt-x86_64/bin/clang.exe` (newest first,
`windows_llvm_mingw_home_bin_dirs_v1`) after the env vars and before PATH.
On the PATH probe a clang whose `-dumpmachine` ends in `-msvc`
(`windows_clang_triple_is_msvc_v1`, e.g. Program Files LLVM) is skipped; if
it is the only clang found, detection fails with the named diagnostic
`[cc-detect] error: only MSVC-flavoured LLVM found (...)`
(`windows_only_msvc_llvm_diagnostic_v1`) instead of a broken GNU link.
Spec: `test/01_unit/compiler/backend/windows_llvm_mingw_default_spec.spl` (4/4).
Native verification (env vars unset, hello-world native-build) still pending.

## Fix

- `runtime_windows_cached_compile_and_publish_v1` (`runtime_object_cache_windows.spl`)
  compiles one TU and publishes it right away through the single-key
  `runtime_windows_cache_publish_batch_v1`. That keeps the per-TU toolchain
  identity re-check. On a mismatch the TU fails with "toolchain changed".
- `compile_runtime_objects` uses it, so a killed run keeps every finished TU and
  the next run resumes from there. It also prints a `[runtime-c] k/N name`
  progress line per TU, so the link phase no longer looks frozen.
- Consequence: a 900 s lane may still die once on a cold cache, but it resumes
  monotonically. A lane with a budget of at least 1000 s completes on the first run.

## Tests

`test/01_unit/compiler/backend/runtime_object_cache_windows_gnu_spec.spl`,
describe "Windows runtime cache per-TU publish (killed-run progress)":
run 1 compiles with no batch publish ("killed"), run 2 must hit with zero
plan/preprocess/compile spawns. The old no-publish path fails this case (9/10).
The fixed path passes 10/10. A failed compile publishes nothing.

## Follow-ups (not in this change)

- The Windows cache path is serial: parallelise it.
- A warm run still takes ~240 s in the link phase for 45 cache hits. Profile
  `runtime_windows_direct_manifest_lookup_v1` and the dep re-hashing.
- `cli_main.exe run <file>.spl` printed nothing at all for a two-line probe
  within 90 s.
