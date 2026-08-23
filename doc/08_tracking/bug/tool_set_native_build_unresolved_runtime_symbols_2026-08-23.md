# Whole tool set fails native-build on unresolved C-runtime symbols (2026-08-23)

Status: OPEN (one sub-defect FIXED in this commit, see §Fixed)

## Summary

**None of the five tools in the tool set can be `native-build`-ed today**, with
either the Rust seed or a genuine pure-Simple stage-2 compiler. Every failure is
the fail-closed unresolved-runtime-symbol check refusing to link — the same
NULL-GOT-then-SIGSEGV class as `rt_unwrap_or_trap` in
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.

The check is doing its job: it is preventing five broken binaries from shipping.
The defect is the missing runtime symbols, not the guard.

## This is NOT seed-specific — measured both ways

Initial hypothesis was a stale source list in the Rust seed
(`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`), since the
pure-Simple backend's own list
(`src/compiler/70.backend/backend/runtime_compiler.spl:366`) already names the
missing translation units. **That hypothesis is refuted by direct measurement.**

| tool | entry | seed rc / missing | stage2 rc / missing |
|---|---|---|---|
| simple_mcp_server     | `src/app/mcp/main.spl`             | 1 / 69 | 1 / 69 |
| simple_lsp_mcp_server | `src/app/simple_lsp_mcp/main.spl`  | 1 / 9  | 1 / 9  |
| t32_mcp_server        | `src/app/t32_mcp_server/main.spl`  | 1 / 75 | 1 / 75 |
| t32_lsp_mcp_server    | `src/app/t32_lsp_mcp/main.spl`     | 1 / compile error | 1 / compile error |
| sj                    | `src/app/sj/main.spl`              | 1 / 10 | 1 / 10 |

Identical counts on both compilers. The confound of passing a seed-built
`--runtime-path` to the stage-2 run was removed and re-measured: stage2 building
`simple_lsp_mcp_server` with **no** `--runtime-path`, its own cache scope and its
own cache dir still fails with the same 9 symbols. So the gap is in the shared
core-C runtime archive composition, reachable from both front ends.

Control: both compilers `native-build` and run a hello world successfully
(rc 0, prints `Hello World`), so the pipeline itself is healthy.

## Buckets

Taken from `simple_mcp_server`'s 69, classified by compiling each candidate C TU
and intersecting its `nm --defined-only` output with the missing set.

- **A1 — `rt_text_is_ascii`** (1 symbol). Defined in `src/runtime/runtime_simd_case.c`,
  which was never an archive member. Zero symbol collisions against the existing
  16 members. **FIXED in this commit.**
- **A2 — mmap / advisory-lock / stat family** (7 symbols: `rt_mmap`, `rt_munmap`,
  `rt_msync`, `rt_madvise`, `rt_file_lock`, `rt_file_unlock`, `rt_file_stat`).
  Bodies live in `src/runtime/platform/unix_common.h`, pulled in only by
  `src/runtime/runtime.c`, which the core-C lane **deliberately excludes** —
  `runtime_legacy_core.c` exists precisely to be the minimal replacement, and
  `runtime.c` overlaps it on 88 symbols, so it cannot simply be added to the
  list. A separate TU that just includes `platform/platform.h` was prototyped
  and rejected: it defines 6 of the 7 but collides on 21 symbols already emitted
  by `runtime_legacy_core.o` (9), `runtime_native.o` (9) and `runtime_process.o` (3).
  **Deciding which TU owns the `platform.h` bodies in the core-C lane is an
  architectural call, not a minimal fix — hence filed, not fixed here.** This is
  the highest-impact remaining item: it alone blocks 3 of the 5 tools
  (`simple_lsp_mcp_server` 9, `sj` 10, and it is a subset of `simple_mcp_server`'s 69).
- **B — undefined in any C runtime** (61 symbols): ~55 `rt_simd_*` lane kernels,
  `rt_utf8_validate` / `rt_utf8_count_codepoints` / `rt_utf8_find_invalid`,
  `rt_array_sort`, `rt_file_mmap_read_bytes` / `rt_file_mmap_read_text`. These
  exist only in the **Rust** runtime (`src/compiler_rust/runtime/`) or, for
  `rt_array_sort`, in `src/runtime/simple_core/core_array_query.spl`. An
  exhaustive scan of owned C (`src/runtime/**/*.c`, excluding `vendor/`) found
  **zero** definitions for any of the 61. This is the same population the
  ADVISORY-RED `scripts/check/check-no-unresolved-runtime-symbols.shs` already
  reports (83 codegen-emitted names undefined in the C runtime archive); tracked
  there, not re-filed.
- **C — `t32_mcp_server`'s `rt_cli_*`** (`rt_cli_dispatch_rust`,
  `rt_cli_handle_compile`, …). These are Rust-seed CLI hooks with no C
  counterpart by construction. **Structural, not a defect** — this tool's closure
  reaches the seed's CLI surface, so it cannot be core-C native-built at all
  until that dependency is broken. Distinguished here so it is not counted as a
  runtime gap.
- **D — `t32_lsp_mcp_server`** fails to *compile*, not link, and it is a
  **layering violation, not a runtime gap**. `src/app/t32_lsp_mcp/tools.spl:5-8`
  does `use cmm_lsp.cmm_parser` / `cmm_analyzer` / `cmm_commands` /
  `cmm_diagnostics`, and the only `cmm_lsp` implementation in the tree is
  `examples/10_tooling/trace32_tools/cmm_lsp/`. A product tool under `src/app/`
  therefore depends on `examples/`. Bounding the build to the real source roots
  (`--source src/compiler --source src/app --source src/lib`) does not help — it
  makes the failure *sharper*:
  `hir: cannot resolve import 'cmm_lsp.cmm_parser': ... module path segment`.
  Fix is to move `cmm_lsp` into `src/lib` (or `src/app/cmm_lsp`) and leave the
  examples copy as a consumer, not the provider. Filed here; not fixed in this
  commit because relocating a module is a larger change than this lane's scope.

  Two secondary observations from the same log, recorded so they are not lost:
  - The failure message is degenerate — the failing path is printed three times
    concatenated with no line/column, and the actual diagnostic only appears
    further into the string. A `FAILED FILES` entry should carry one path plus
    one diagnostic with a position.
  - `--entry` without `--source` silently scans the whole project, which is how
    an unrelated `examples/` file first appeared to be at fault. The compiler
    does emit a `note:` about this, which is good; the note is what made the
    misdiagnosis recoverable.

## Fixed in this commit

`runtime_simd_case.c` added to the seed's core-C `runtime_inputs`
(`tools.rs`), mirroring the pure-Simple backend list. Pinned by a new
archive-membership assertion in
`pipeline::native_project::tests::test_core_lane_runtime_archives_expose_required_abi_symbols`,
following the existing `simd_text_init` / `rt_thread_available_parallelism`
precedent in that test.

**Honest scope: this unblocks zero tools end-to-end.** After it,
`simple_mcp_server` still misses 68, `simple_lsp_mcp_server` 8, `sj` 9. It
removes one symbol from the wall and stops that TU regressing again.

## Source-mode baseline (for contrast)

`sh scripts/check/build-and-verify-tools-with.shs <seed>` reports
`PASS — 6 tool(s) verified`, with real MCP `initialize` handshakes over stdio for
`simple_mcp_server`, `simple_lsp_mcp`, `t32_lsp_mcp`. That script drives the
compiler's `run` subcommand, which compiles the tool's source closure at process
start. **It is therefore a seed-`run` proof, not a native-build proof** — and it
cannot be pointed at a real stage-2 binary at all, because the bootstrap CLI
(`src/app/cli/bootstrap_main.spl`) exposes only `compile` and `native-build` and
has no `run`. Its `TOOLS_NATIVE_BUILD=1` branch is a stub that SKIPs. The green
verdict there and the five red native builds here are consistent, not contradictory.

## Repro

```sh
# with either binary; stage2 needs no --runtime-path
<compiler> native-build --target x86_64-unknown-linux-gnu --backend llvm \
  --runtime-bundle core-c-bootstrap --entry-closure \
  --entry src/app/simple_lsp_mcp/main.spl --cache-dir <own> --threads 4 -o /tmp/out
# => Build failed: 9 runtime symbol(s) ... rt_file_lock, rt_mmap, ...
```

`--runtime-bundle auto` and `core-c-bootstrap` give identical results.

## Notes for the next lane

- The Rust seed silently downgrades `--mode dynload` to one-binary
  (`E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED`); a stage-2 does not.
- Do not reach for `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` or add bucket B to
  `RT_OPTIONAL_SYMBOLS`. Either converts this fail-closed link error back into
  the NULL-GOT SEGV that the guard exists to catch.

## Discriminating proof for the fix

The assertion was proven to fail pre-fix by reverting **only** the `tools.rs`
hunk (the `runtime_simd_case.c` entry) and leaving the test edit in place:

```
PRE-FIX  (tools.rs hunk reverted, test kept):
  panicked at compiler/src/pipeline/native_project/tests.rs:2086:5:
  core-c runtime archive must include runtime_simd_case.c ...
  test result: FAILED. 0 passed; 1 failed          exit 101

POST-FIX (both edits in place):
  test result: ok. 1 passed; 0 failed              exit 0
```

Test: `pipeline::native_project::tests::test_core_lane_runtime_archives_expose_required_abi_symbols`.

## Sanity results (source mode, real MCP handshakes)

Exit status read into a variable on the line after each invocation, never
through a pipe. A passing `--version` was never accepted as a pass.

| server | verdict | rc | handshake latency | peak RSS |
|---|---|---|---|---|
| simple_mcp_server     | OK | 0 | 16335 ms | 208872 KB |
| simple_lsp_mcp_server | OK | 0 |  3374 ms |  89588 KB |
| t32_lsp_mcp_server    | OK | 0 | 15628 ms | 131732 KB |

No earlyoom SIGKILL (137/143) was observed in any run in this lane.

Note the apparent tension with bucket D: `t32_lsp_mcp_server` handshakes fine in
source mode yet cannot be native-built. That is consistent — `run` scans the
whole project by default, so it finds `examples/.../cmm_lsp`, while a build
bounded to real source roots correctly does not. It is further evidence that the
`examples/` dependency is real rather than an artifact of how it was invoked.

`t32_mcp_server` is deliberately absent from the table: without a packaged
TRACE32 install it prints a readiness banner and exits, so an `initialize`
handshake cannot pass on a T32-less host. That is an environment limitation,
recorded as such rather than reported as a pass or a failure.
