# Stage4 Stub-Symbol Inventory + Fix Plan (2026-07-11)

Pure-analysis companion to `redeploy_stage4_plan_2026-07-08.md`'s "STATUS NOW"
(822-symbol stub wall). This doc classifies the full stub set and proposes an
ordered, verifiable fix plan. **No builds/edits performed while writing this —
analysis only.**

## Data sources (and a caveat on symbol-count drift)

The current documented-blocking run is
`build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`
(2026-07-11T06:51, `Generating 822 stub functions...`), but that log only
prints an 80-symbol preview, not the full list — Rust-side, the full list is
only written to disk when `SIMPLE_DUMP_STUBS=<path>` is set
(`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:684-689`).
No such dump exists for the exact 822-symbol run. The closest artifact that
*does* have a complete, sorted symbol list is
`build/bootstrap/logs/aarch64-apple-darwin/stage4-stub-symbols.txt` (1052
symbols, captured 2026-07-10T22:27 from the sibling
`stage4-native-build.retry-stub-dump.log` run, `Generating 1052 stub
functions`). Across the day's 11 captured retries the count fluctuates
107 → 1052 depending on ambient flags/env (see table below) — the pipeline is
not yet flag-stable. The 822-run's 80-symbol preview is a prefix-identical
match against the 1052 list (same alphabetical head), so the two runs are the
same *kind* of build with a partially-overlapping symbol set; this doc uses
the 1052-symbol dump as the analysis base (it is the only complete list) and
calls out where the 822 count likely differs (small deltas from since-landed
fixes, not a different root cause).

| Retry log | Stub count | Linked size | Note |
|---|---|---|---|
| `stage4-native-build.log` (current/documented) | 822 | 52812 KB | no full dump available |
| `.retry-write-at-bool.log` | 825 | — | |
| `.retry-io-runtime-write.log` | 824 | — | |
| `.retry-corec-stub-missing-rt.log` | 824 | 52812 KB | |
| `.retry-cli-ops.log` | 824 | — | |
| `.retry-run-code-direct-write.log` | 823 | — | |
| `.retry-stub-dump.log` / `.retry-stub-missing-rt.log` | **1052** | — | full list captured (`stage4-stub-symbols.txt`) |
| `.retry-hosted-runtime.log` | **112** | **62150 KB** | see § Highest-leverage fix |
| `.retry-page-aligned.log` | 109 | 52781 KB | |
| `.retry-no-app-string-builder.log` | 107 | 52780 KB | |

The `retry-hosted-runtime`/`retry-page-aligned`/`retry-no-app-string-builder`
runs (107-112 stubs, larger 62MB binary) prove a ~700-symbol resolution is
achievable by linking a different/fuller runtime archive — see the
highest-leverage fix below, independently reproduced from first principles
(archive symbol diff), not just inferred from these logs.

## Bucket table (base: 1052-symbol dump)

| Bucket | Count | Root cause | Fix locus |
|---|---|---|---|
| `rt_*` GPU/graphics backends (cuda, vulkan, rocm, oneapi, opengl, opencl, webgpu, metal, sdl2) | 130 (of 536 genuinely-nowhere-defined; see below) | **(c) over-linking.** CLI entry never calls these; native-build's undefined-symbol scan runs *before* the linker's section GC (`stubs.rs:647-649` comment: "sees references from unreachable functions"), so declaring the extern anywhere in `--source src/lib` pulls it into the must-resolve set even though the CLI closure never reaches it. | `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` — reorder scan-after-GC, or gate `--source` globbing so CLI native-build doesn't compile `gc_async_mut/{cuda,gpu,torch}` etc. into the closure at all (entry-closure walk should already prune this — investigate why `--entry-closure` isn't excluding these). |
| `rt_*` OS/HW-specific (win32, cocoa, kqueue, iocp, arm/virtio, mmio, dma, volatile) | 70 (of 536) | **(c) over-linking** — same mechanism, platform-conditional code (Windows IOCP, ARM virtio-blk MMIO) compiled in on macOS/arm64 host. | Same locus as above; alternatively `cfg`-gate these Simple modules per-target so they're not even parsed into the entry closure on a non-matching host. |
| `rt_*` cranelift/JIT/SMF-cache internals | 78 (of 536) | **(c) over-linking** or **(a) genuinely unimplemented** — needs a closer look; these are compiler-internal JIT-execution-path externs (`rt_cranelift_*`, `rt_jit_*`, `rt_smf_*`) that a *CLI* build (as opposed to a JIT/REPL build) may legitimately not need at link time if section GC ran first. | Same as above (scan-after-GC) is the general fix; if any remain live after GC, they're bucket (a) and need real runtime impls. |
| `rt_*` sqlite | 27 | Likely **(c)**: sqlite FFI only reachable from `std.database`, not the base CLI. | Same scan-after-GC fix. |
| `rt_*` http | 22 | Likely **(c)**: only reachable from `std.net.http`, not core CLI paths. | Same scan-after-GC fix. |
| **`rt_*` core runtime already resolvable — file/string/array/math/value/cli/io/dir/env/dict/log/process/typed/tuple/event/host** | **405** (of 941 `rt_*` total) | **(a), but a build-plumbing bug, not a missing implementation.** These symbols exist and are `T`-defined in `src/compiler_rust/target/debug/deps/libsimple_runtime.a` (verified via `nm`) but are **absent** from `src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a` (391 T-symbols total) — the archive stage4's own driver actually links against, since the stage2 seed binary (`SIMPLE_BINARY=.../stage2/.../simple`) resolves its runtime archive relative to the bootstrap tree. The bootstrap-lane archive is stale/partial. | `src/compiler_rust/compiler/src/pipeline/native_project/config.rs` (`resolve_runtime_lane`, `selected_runtime_library`, `find_abi_complete_simple_core_runtime_library`) + whatever step produces `target/bootstrap/deps/libsimple_runtime.a` — needs to build/select the same complete archive the `debug` lane uses (22576 T-symbols) instead of the 391-symbol bootstrap one. **THIS IS THE HIGHEST-LEVERAGE SINGLE FIX** — see below. |
| bare (`rt_`-less) `file_*`/`dir_*`/`path_*`/`glob_*`/`walk_dir` externs | 22 | **(b) naming-mismatch bug.** `src/lib/nogc_sync_mut/fs.spl:617-639` (and the identical block in `src/lib/nogc_async_mut/fs.spl:~617`) declares `extern fn file_read_text(path: text) -> text?`, `extern fn path_parent(...)`, `extern fn dir_read(...)`, etc. with **no `rt_` prefix**, while every actual runtime implementation is `rt_file_read_text`, `rt_path_parent`, `rt_dir_read`. No `@extern("rt_...")`-style rename attribute exists in this codebase (grepped, none found), so these externs literally look for undefined bare-named C symbols that don't exist anywhere — not even in the complete debug archive. | `src/lib/nogc_sync_mut/fs.spl:617-639`, `src/lib/nogc_async_mut/fs.spl` (duplicate block) — rename the `extern fn` declarations to the `rt_`-prefixed names (or add thin Simple wrappers: `extern fn rt_file_read_text(...) -> text?` + `fn file_read_text(path) -> text?: rt_file_read_text(path)`), matching the pattern already used correctly in `nogc_sync_mut/io/file_ops.spl`, `nogc_sync_mut/ffi/io.spl`, `nogc_sync_mut/fs/__init__.spl`, which each define a *wrapper* `fn file_read_text` over the `rt_`-prefixed extern rather than re-declaring the bare name as extern. |
| `_dot_`-mangled trait/enum-variant methods (`BidirHirExpr_dot_*` ×8, `Iterator_dot_rfind`/`is_empty`, `Write_dot_write_all`) | 11 | Compiler-internal HIR/trait dispatch — visitor-pattern methods on the `BidirHirExpr` enum and default trait methods (`DoubleEndedIterator::rfind`, `ExactSizeIterator::is_empty`, `Write::write_all`) that aren't monomorphized/emitted for this entry closure. Likely **(c)** dead code from an unused HIR path, but needs a source-level confirmation before assuming safe-to-drop. | `src/compiler/` HIR bidir-typing module (search for `BidirHirExpr`) + trait-default-method lowering in the seed/compiler; investigate whether `BidirHirExpr` variants are reachable from `src/app/cli/main.spl`'s closure at all. |
| `module__Class` type-descriptor symbols (`backend__codegen__Jit*` ×4, `driver__*` ×2, `nogc_async_mut__io__SyncTcp*` ×2, `os__services__vfs__*NvfsHostedDriver` ×3, `tools__leak_check__main__MemLeakEntry`) | 12 | Class/struct type-descriptor or vtable symbols referenced (likely via reflection/generic instantiation) but whose defining module isn't in the compiled closure — same GC-before-scan mechanism as bucket (c) above, or a genuine cross-module reflection gap. | Same scan-after-GC fix as primary remedy; `tools/leak_check`, `os/services/vfs/*HostedDriver` look like debug/OS-only tooling not needed by the plain CLI — confirm dead and safe to exclude from `--source` glob. |
| misc single symbols (`panic`, `_rust_eh_personality`, `_dealloc`, `copy_mem`, `chars_len`, `serial_println`, `stdin_read_char`, `input_chars/trim`, `json_serialize/pretty`, `lexer_tokenize`, `mem_enable/disable/snapshot/dump_leaks`, `hash_to_upper_hex`, `selector_*` ×11, `predicate_*` ×4, stitch-design-system helpers, `simpleos_fat32_*`, `wm_input_event`, `run_check`/`run_arch_check`, `tokens_len/push`, `parts_len`, `trimmed_len`, `unsafe_addr_of`, `emit_push_payload_sdn`, `pred_tokens_push`) | ~55 | Mixed: some are the **same bare-vs-`rt_`-prefix bug** as the file/dir/path bucket (`panic` vs `rt_panic`? — needs a grep check per-symbol), some are genuinely freestanding/OS-kernel-only (`serial_println`, `simpleos_fat32_*`), some are dead tooling code (`selector_*`/`predicate_*` look like a query-DSL AST reachable only from an unused analysis tool, stitch-design-system helpers are a Stitch-integration feature not part of core CLI). Needs per-symbol triage before batch-fixing. | Case-by-case; start by grepping each for a `rt_`-prefixed sibling (fast mechanical win), then bucket the remainder as freestanding-only / dead-tool exclusions. |

Sanity check: rt_-prefixed buckets above (130+70+78+27+22+405+misc rt_) plus
non-rt buckets (22+11+12+~55) should reconcile to 1052; the "still genuinely
missing from every archive" set is 641 symbols (536 `rt_` + 105 non-`rt_`,
confirmed via `comm -23` against the debug archive's symbol table), and the
"resolvable today by linking the right archive" set is 411 symbols (405
core-runtime `rt_*` + 6 misc: `spl_dlclose/dlopen/dlsym`,
`spl_thread_cpu_count`, `spl_wffi_call_i64`, `stdin_read_char`).

## Highest-leverage single fix

**Link stage4 native-build against the complete runtime archive instead of
the stale bootstrap-lane one.**

Evidence (all directly measured, not inferred):
- `nm src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a` → **391**
  `T`-defined symbols (this is the archive stage4 actually links, since its
  driver is the stage2 seed at `build/bootstrap/stage2/aarch64-apple-darwin/simple`,
  which resolves its runtime archive relative to the bootstrap tree).
- `nm src/compiler_rust/target/debug/deps/libsimple_runtime.a` → **22,576**
  `T`-defined symbols (built later — 2026-07-11T00:28 vs the bootstrap
  archive's 2026-07-10T23:09 — and complete for this purpose).
- Of the 1052 stub symbols, **405 `rt_*` + 6 misc = 411** are already
  `T`-defined in the debug archive and **0** are defined in the bootstrap
  archive — i.e., relinking against the debug-lane archive (or rebuilding the
  bootstrap-lane archive with the same completeness) mechanically resolves
  ~39% of the stub wall (411/1052, or proportionally ~322/822 on the current
  count) with **zero Simple-source changes**.
- This is independently corroborated by the day's own
  `retry-hosted-runtime`/`retry-page-aligned`/`retry-no-app-string-builder`
  logs, which used some other runtime-selection path and saw the stub count
  fall to 107-112 (a ~710-symbol drop) — consistent order of magnitude with
  "link the complete archive," though those specific runs used the
  now-explicitly-refused `hosted` runtime-bundle option
  (`config.rs:38-43,111-119,155-158`: `"native-build removed Rust-hosted
  runtime bundles; use simple-core or core-c-bootstrap"`), so they are not a
  directly reusable recipe — the fix must go through the `simple-core` or
  `core-c-bootstrap` lane's archive-selection/build step instead
  (`config.rs:72-260`, `tools.rs:197+` `build_core_c_runtime_library`,
  `find_abi_complete_simple_core_runtime_library`).

Fix locus: `src/compiler_rust/compiler/src/pipeline/native_project/config.rs`
(`resolve_runtime_lane`, `selected_runtime_library`) and
`tools.rs` (`find_simple_core_runtime_library`,
`runtime_archive_has_core_required_symbols`,
`build_core_c_runtime_library`) — whichever lane stage4's bootstrap-tree
build actually resolves to needs to either (a) rebuild its archive from the
same complete symbol set as `target/debug/deps/libsimple_runtime.a`, or (b)
have its lane-selection logic prefer that complete archive over the stale
391-symbol one when both exist. **Estimated blast radius: >100 symbols
(measured 405-411), single largest lever in this inventory.**

## Ordered fix plan

1. **Runtime-archive completeness (highest leverage, ~400+ symbols).**
   Diagnose why `target/bootstrap/deps/libsimple_runtime.a` (391 T-symbols,
   built 2026-07-10T23:09) is far smaller than `target/debug/deps/libsimple_runtime.a`
   (22,576 T-symbols, built 2026-07-11T00:28) — likely a stale/partial
   bootstrap-lane build, or the bootstrap lane intentionally builds a minimal
   subset and stage4 should instead route through the `simple-core`/
   `core-c-bootstrap` lane with `find_abi_complete_simple_core_runtime_library`
   returning a real hit. Rebuild or reroute so stage4 links the complete
   archive. Re-run stage4 native-build and re-diff the stub count.
2. **Fix the bare-vs-`rt_`-prefixed extern mismatch (~22+ symbols, bucket b).**
   `src/lib/nogc_sync_mut/fs.spl:617-639` and the `nogc_async_mut/fs.spl`
   twin: rename externs to their `rt_`-prefixed forms (matching
   `nogc_sync_mut/io/file_ops.spl`'s already-correct wrapper pattern) or
   route through a thin wrapper. Grep the remaining ~55 "misc" bucket for the
   same bare/`rt_` mismatch pattern first — likely more of that ~55 resolves
   the same mechanical way.
3. **Scan-after-GC / entry-closure tightening (bucket c, potentially the
   largest remaining bucket — 130+70+78+27+22+12 ≈ 339 symbols).**
   Investigate `stubs.rs`'s own documented caveat ("scan runs before the
   linker's section GC, so it also sees references from unreachable
   functions") — either move the undefined-symbol scan to run after a
   dead-code-elimination pass, or verify `--entry-closure` is supposed to
   already exclude GPU/Windows/kernel-only modules from a CLI build and fix
   why it isn't. This is compiler-pipeline work (Rust seed side,
   `native_project/`), not a Simple-source fix — flag for peer review before
   starting, since it touches the shared native-build path used by every
   target, not just stage4.
4. **`_dot_`/type-descriptor triage (23 symbols, low leverage but needed for
   a clean 0-stub build).** Confirm `BidirHirExpr` variants and the
   `module__Class` descriptor symbols are actually unreachable from the CLI
   closure (if step 3's scan-after-GC fix lands, this bucket may resolve
   automatically as a side effect — check before doing separate work).
5. **Re-run the exact gate** (`stage4-native-build.log`'s command line) after
   each step and re-diff the stub list against this doc's bucket table to
   confirm the predicted reductions before moving to the next step.

## Caveats / things this analysis could NOT verify (need a build to confirm)

- The exact 822-symbol list for the *current* documented run was never fully
  dumped to disk; all counts above are computed against the 1052-symbol
  proxy list. The bucket proportions should carry over closely (the 80-item
  preview is a verified alphabetical-prefix match), but exact per-bucket
  counts for the literal 822 may differ by a few symbols per bucket.
- Whether the ~339 "bucket c" symbols are truly dead (safe to exclude) vs.
  reachable-but-currently-unresolved needs a real re-run with
  `SIMPLE_DUMP_STUBS` set and `--strict-no-stub-fallback` semantics compared,
  since the object scan's pre-GC visibility means "still undefined after a
  runtime-archive fix" is the honest test, not source-reading alone.
