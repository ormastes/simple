# Windows aarch64-pc-windows-gnullvm cross link takes 8-12 min: serial tool spawns, not lld

- **Status:** verification-pending
- **Date:** 2026-11-18
- **Lane:** winarm-linkperf
- **Area:** Rust seed native-build link (`src/compiler_rust/compiler/src/pipeline/native_project/{linker,stubs}.rs`)

## Symptom

Seed (built with llvm-mingw, `x86_64-pc-windows-gnullvm`) `native-build ... --target aarch64-pc-windows-gnullvm`:

- `src/app/test_runner_new/main.spl`: `17.4s compile + 692.1s link`
- a one-line hello: `0.1s compile + 658.6s link`; re-measured with a process sampler: 470.6 s link

A one-line hello costs almost as much as the test runner, so the cost does not depend on the program's object count.

## Profile (process sampler, 2 s polls of the seed's child tree, hello, arm64)

| t (s) | phase | spawns |
|---|---|---|
| 1-115 | core-C runtime supplement compiled from source (`build_c_runtime_library`, build dir under per-link `temp_dir`) | ~65 `clang -c` |
| 136-302 | `gnu_link_line_libraries`: one `clang --target=aarch64-w64-windows-gnu -print-file-name=lib<X>.a` per library, serial (`libmsvcrt`/`libkernel32` asked twice) | 27, ~6 s each |
| 302-424 | `stubs::scan_defined_symbols`: one `llvm-nm` per system import lib, serial | ~25 (short-lived; sampler caught 1) |
| 442-456 | the real `clang -fuse-ld=lld` link | 1, **~14 s** |

So lld-link itself, a COFF relocatable merge and archive extraction are not the cause. The time goes to process spawns run one after another, at ~5-6 s per spawn on this loaded Windows host.

x64 hello (`x86_64-pc-windows-gnullvm`, same host, same hour): 294 s link. It has the same phases (16 `-print-file-name` spawns over t=85-221, ~67 s of nm, an lld step of a few seconds). arm64 pays more because none of its libs are in the `-L` dirs, which point at x64 libraries, so every lookup falls through to the driver.

## Fix (this change)

1. `resolve_gnu_link_libraries`: after the driver answers once, the parent directory of that answer is searched on disk before the driver is asked again (llvm-mingw keeps every target lib in `<triple>/lib`). Names are deduplicated, and `-L` dirs keep precedence. 27 spawns become 1-2.
2. `scan_defined_symbols`: the per-library `nm` calls run on the rayon pool, and their results are collected into separate per-library sets and merged afterwards (lockless).

Tests (`linker_tests`): `gnu_link_libraries_ask_driver_once_per_sysroot_dir` (repro; it fails on the old per-library loop with 7 calls instead of 1) and `gnu_link_libraries_keep_l_dir_precedence_and_fall_back_to_driver` (similar pattern: `-L` precedence, a lib outside the learned dir, and a missing lib).

## Not fixed (next levers)

- The core-C supplement is rebuilt on every link (~100 s), because its build dir is under the per-link `temp_dir`, so the fingerprint cache in `build_c_runtime_library` can never hit. Fix: give it a stable, fingerprinted, per-target and per-cache-scope dir.
- `tools.rs::stage4_system_library_path` has the same one-spawn-per-lib `-print-file-name` pattern (Stage 4 lane only).
- The seed hands roots to lld through `-Wl,-u` response files. That cost is negligible here.

## Measurements

Same host, before and after runs back to back (2026-11-18 ~09:45; the host was less loaded than at the time of the 470-692 s runs):

| input | before link | after link | output |
|---|---|---|---|
| hello, arm64 | 70.8 s | 18.0 s | 536 KB, both |
| test_runner_new, arm64 | 59.2 s | 39.6 s | 7025 KB, both |

Each spawn costs more as host load rises (~6 s each under load), so the saving scales with load. Peak working set of the largest sampled process: 2.48 GB before, 0.83 GB after. This is a 2 s-poll sample, so treat it as no-regression evidence, not as a precise figure. RSS: the seed's peak working set is reported from `Win32_Process.PeakWorkingSetSize`. `elf_link_rss_budget.shs` gates the pure-Simple ELF linker, which this change does not touch.
