# Seed native-build of stage 2 (windows-gnu, LLVM): runaway RSS after the CLANG64 libLLVM-23 switch

- **Date:** 2026-10-23
- **Status:** open. The cause is a suspect, not proven. Nothing was rebuilt, because the host is shared.
- **Process:** the Rust seed, `stage2-runtime-authority/simple.exe native-build`. It is not a Simple-compiled compiler.
- **Evidence:** `C:/dev/wt-rel3-new/build/rss/jobs40.curve`

## Symptom

The seed `native-build` compiles the 1,488-file stage-2 closure for x86_64-pc-windows-gnu. Flags: LLVM, `--entry-closure`, `--mode dynload`, which falls back to one-binary.

| seed tree | LLVM | jobs | RSS |
|---|---|---|---|
| `8aaa2501af6` | MSVC LLVM 23.1.1 (`LLVM-C.dll`) | 16 | peak about 10 GB |
| `658410feaaf` | MSYS2 CLANG64 23.1.3 `libLLVM-23.dll` | 24 | 56 MB, then 1.4 GB, 4.7 GB and 27 GB in about 4 minutes |
| `658410feaaf` | same | 40 | 41 GB at 745 s, 61 GB at 778 s, 82 GB at 811 s (about 600 MB/s); killed |

At 24 jobs RSS grows as fast as at 40. In the 40-job curve, RSS stays under 300 MB until about 490 s and then grows steadily. That shape is a cumulative leak or retention. A wider fan-out would instead show a high plateau.

## Ruled out: the `b065988b5a2` transient-promotion change

An earlier draft of this record blamed `b065988b5a2`, which changed `rt_transient_heap_promote` (`runtime/src/value/collections.rs:2877-2885`). That cannot cause growth in **this** process:

- The seed reaches `rt_transient_heap_promote` only through the interpreter extern `compiler/src/interpreter_extern/memory.rs:442`. `native-build` does not run `.spl` through the interpreter. `compile_file_safe` (`pipeline/native_project/compiler.rs:1100-1200`) borrows only the parsed-source cache from the interpreter module.
- A transient heap scope is opened only by Simple code at run time, so `TRANSIENT_HEAP_SCOPE` stays empty in the seed.
- The concern still applies to the **stage-2 binary at run time**. The per-file `parser_promote_transient_owners` (`src/compiler/10.frontend/core/parser.spl:158-166`) now promotes `par_errors`, `par_warnings` and `par_struct_names` on every file. Those arrays are reassigned per file (`parser.spl:342-344`), so each file's promoted copies are orphaned. This is worth a separate check of stage-2 compile RSS. It is not this bug.

## Seed delta between the two trees

`git diff 8aaa2501af6 658410feaaf --stat -- src/compiler_rust` shows 11 files, +337/-11:

- No change in `native_project/compiler.rs`, `mod.rs`, the parsed-source cache, `module_cache.rs` or the codegen backends.
- `native_project/linker.rs` and `stubs.rs`: link-line and stub-scan changes for gnu system libraries. These run only at link time, after the compile phase, so they do not explain growth during compilation.
- `interpreter_extern/memory.rs`: byte-array interpreter twins. Not on the native-build path.
- `runtime/.../collections.rs`: the promotion change ruled out above.
- **`vendor/aya-llvm-sys/build.rs` (`40be663df96`)**: on non-MSVC Windows targets, the seed now links `libLLVM-23.dll` from MSYS2 CLANG64 instead of MSVC `LLVM-C.dll`. It is the only change that touches code running during the compile phase. Every worker's whole LLVM pipeline now runs in a different LLVM build (CLANG64 23.1.3), with a different C++ runtime and allocator (libc++ on UCRT malloc, instead of the MSVC CRT heap).

## Leading hypothesis

Each worker builds and drops an `inkwell::Context` per file (`compiler.rs` `compile_file_to_object`). The seed itself uses mimalloc (`driver/src/main.rs:69-72`), but LLVM's allocations happen inside `libLLVM-23.dll` and use its own CRT heap.

So one of these is the likely cause:

- **(a)** Freed memory is not returned under concurrent create/destroy across short-lived threads. Each file gets a fresh `std::thread`. That makes growth follow throughput: 24 and 40 jobs grow at the same rate, which matches.
- **(b)** The CLANG64 libLLVM build retains or leaks per-context state that the MSVC build freed.

The thread count is not the variable. The 16-thread baseline is from the **old** tree, and no 16-thread run exists on the new tree.

## Experiments to confirm (cheap, run when the host is free)

1. Run `658410feaaf` at `--threads 16` with RSS sampling. If it still runs away, thread count is ruled out and the toolchain is confirmed as the variable.
2. Build the same tree with only `40be663df96` reverted (MSVC `LLVM-C.dll`) and run at 24 jobs. If RSS goes back to about 10 GB, the cause is pinned.
3. Run with `SIMPLE_NATIVE_FILE_TIMING=1` and correlate the RSS jumps with files. If memory never drops between files, the cause is retention, not peak size.

## Smallest fix (if experiment 2 confirms)

- **Short term:** for the windows-gnu seed build, link the seed against the MSVC-ABI `LLVM-C.dll` only for the codegen worker path, or go back to the previous LLVM until (3) isolates the cause. As a guardrail, set `SIMPLE_MEMORY_LIMIT_MB=60000` on the bootstrap lane. That turns a host OOM into a clean fail.
- **Structural:** reuse one LLVM context per rayon worker instead of one fresh `std::thread` plus context per file. That is the spawn in `compile_file_safe`, `compiler.rs:1118-1125`. Thread-local or arena heaps in the DLL CRT then stay bounded by the worker count.

## Seed threading and admission (checked)

- `compile_entries_parallel` (`compiler.rs:456-545`) runs on a rayon `par_iter`, with a fresh thread per file.
- Object files are written straight to disk (`compiler.rs:524-525`).
- `ModuleImports` (`mod.rs:545+`) is made of `Arc` fields, and the suffix index is shared once (`compiler.rs:478`). No whole-graph structure is cloned per worker.
- A timed-out worker cannot be cancelled (`wait_for_compiler_thread`, `compiler.rs:1243-1265`).
- `NativeCompileAdmission` (`compiler.rs:1080-1098`) is only a timeout latch. It is not a memory budget.

## Existing knobs that bound memory today

- `--threads N`, `SIMPLE_BOOTSTRAP_THREADS` and `--low-memory` (1 worker). The default for LLVM is clamped to 4 workers (`mod.rs:299`). None of them is aware of RSS.
- `SIMPLE_MEMORY_LIMIT_MB` (`watchdog.rs:38-42`, `memory_guard.rs:32`) is a hard RSS kill, not admission.
- `SIMPLE_MODULE_RSS_WARN_MB` only warns. `SIMPLE_PARSED_SOURCE_CACHE_MAX` caps the per-worker parse memo (default 256).
- No RSS-aware admission exists. If one is wanted, the place is `NativeCompileAdmission::run`: block admission while RSS is above a `SIMPLE_NATIVE_RSS_BUDGET_MB`.

## Addendum 2026-10-24: Linux runtime confirmation — the stage-2 BINARY leaks at run time

The "worth a separate check of stage-2 compile RSS" note is confirmed on the
Linux lane. Same host, same probe (`src/compiler/bootstrap_admission/p2_add.spl`,
`native-build --backend llvm --runtime-bundle core-c-bootstrap --entry-closure
--mode one-binary`):

| stage-2 candidate | peak RSS | result |
|---|---|---|
| 4ab52ecd1f0 (pre-convergence, no b065988b5a2) | 2.17 GB total | build OK |
| ea1a3a7879a (has b065988b5a2) | 4.06 GB coordinator alone | kernel OOM kill |

Measured with `/usr/bin/time -v` on an otherwise quiet 7.6 GiB host. The
post-change candidate grows past the host's RAM during the MIR phase of a
trivial one-module probe, so the stage-2 sanity battery fails on this host
class with `raw_status=137` (SIGKILL from the kernel OOM reaper; the bounded
collector records `reason=child-signal`). The per-file promotions in
`parser_promote_transient_owners` (par_errors/par_warnings/par_struct_names
are reassigned per file, orphaning each promoted copy) plus per-module HIR
promotions have no release path, so the growth is cumulative per file as the
Windows curve suggests — but here it is fatal within a single small build,
not just on 1,488-file runs.

Workaround for memory-constrained hosts until the release/demote path lands:
none found — disabling the HIR/parse shard workers does not bring the
single-process footprint back under the host budget.
