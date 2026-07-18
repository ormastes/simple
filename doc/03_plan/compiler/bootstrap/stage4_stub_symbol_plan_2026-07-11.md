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

## Step 1 status (2026-07-11, re-investigated): ORIGINAL DIAGNOSIS WAS WRONG — root cause is a broken `nm` on the analysis/build host, not a stale/partial archive

**Correction: `target/bootstrap/deps/libsimple_runtime.a` is NOT stale or
partial. It is essentially complete (~23.5k defined symbols, all core `rt_*`
present) — every "391 T-symbols" / "405 missing core rt_* symbols" figure in
this doc's Data-sources/Bucket-table/Highest-leverage sections above was an
artifact of running the wrong `nm` binary, not a real property of the
archive.**

Evidence:
- `nm src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a` on this
  host resolves to **`/usr/bin/nm`** (Xcode's, LLVM-based reader bundled with
  an older Xcode toolchain). Extracting a single archive member (e.g.
  `simple_runtime.simple_runtime.cb7c9d2922500ad5-cgu.00.rcgu.o`) and running
  `nm` on it directly fails: `error: ... Unknown attribute kind (102)
  (Producer: 'LLVM21.1.8-rust-1.94.0-stable' Reader: 'LLVM
  APPLE_1_1700.6.4.2_0')`. rustc 1.94 emits object files tagged with an LLVM
  21 attribute Xcode's bundled nm/LLVM reader doesn't understand yet. `nm`
  silently drops the unreadable members (no hard error at the archive level,
  just "no symbols"/partial output per member), which is why a naive
  `nm -g --defined-only libsimple_runtime.a` under-reports by ~98% (391 of
  ~23.5k) — it isn't that the symbols are absent, `nm` just can't parse most
  of the object files that contain them.
- Installing/using a matching-generation reader
  (`/opt/homebrew/opt/llvm@22/bin/llvm-nm`, Homebrew LLVM 22.1.2, which can
  read LLVM 21 IR/attributes) on the **exact same, unmodified**
  `target/bootstrap/deps/libsimple_runtime.a` gives **23,562** unique defined
  symbols (**19,994** of type `T`), and `rt_array_all`, `rt_dict_new`, and
  every other symbol from the doc's "405 missing core rt_*" bucket resolve as
  `T`-defined. Diffing the full symbol sets of
  `target/bootstrap/deps/libsimple_runtime.a` vs.
  `target/debug/deps/libsimple_runtime.a` with `llvm-nm` (not system `nm`)
  shows **0 `rt_*` symbols present in debug but missing from bootstrap** — the
  405/411-symbol "highest-leverage fix" bucket in this doc does not exist as
  described. (The two archives do still differ by ~28k non-`rt_` symbols —
  Rust-mangled monomorphizations/dependency-crate internals pulled in by
  whatever built `target/debug` — but none of those are stub-wall symbols the
  CLI closure needs.)
- Verification command used (reproducible, does not touch the archive or the
  repo):
  ```bash
  ln -sf /opt/homebrew/opt/llvm@22/bin/llvm-nm /path/to/shim/nm
  PATH="/path/to/shim:$PATH" nm -g -p src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a | wc -l   # -> 23562 unique names
  PATH="/path/to/shim:$PATH" nm -g -p src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a | grep -E 'rt_array_all$|rt_dict_new$'  # both present as T
  ```

**Consequence for the rest of this doc:** the compiler's own stub-generation
scan has the identical bug, so the 822/1052-symbol stub counts quoted
throughout this doc are themselves suspect and likely inflated for the same
reason — not just the "405 core rt_*" bucket. `stubs.rs` and `linker.rs`
determine "is this symbol already defined in the runtime archive/other
objects" by shelling out to a **hardcoded, unqualified `nm`** (see below),
which resolves to the same broken `/usr/bin/nm` on any host with an
LLVM21-generation rustc and an older Xcode toolchain. Any symbol whose only
defining object happens to live in one of the archive members `nm` can't
parse gets misclassified as "undefined" and a stub gets generated for it even
though the real implementation is already linked in. This plausibly explains
a large fraction of the 822-symbol wall, not only the core-runtime bucket —
buckets (c) "over-linking" and (a) "genuinely unimplemented" in the table
above should be re-audited with a working `nm` before trusting their counts.

### Zero-code verification performed (this session)

Confirmed via the `llvm-nm`-shim commands above; **no repo files, archives, or
Rust seed source were modified**. This was pure read-only analysis using a
symlink in the session scratchpad
(`/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/nm_shim/nm`
→ `/opt/homebrew/opt/llvm@22/bin/llvm-nm`), not wired into the real build.

A durable fix requires a Rust seed source change, so per the task's
instructions it is **proposed below, not applied**.

### Seed diff status (implemented locally, redeploy still pending)

Root cause: `stubs.rs` and `linker.rs` invoke the platform's default `nm`
unconditionally (`std::process::Command::new("nm")`, 4 call sites in
`stubs.rs:138,523,548,572` + 3 in `linker.rs:78,280,317`), instead of
preferring an LLVM-generation-matched reader. `tools.rs::archive_defined_symbols`
(used by `runtime_archive_has_core_required_symbols` /
`find_abi_complete_simple_core_runtime_library`) already has the right idea —
`for tool in ["llvm-nm", "nm"] { ... }` — but even that is insufficient on
this host: Homebrew's `llvm`/`llvm@22` formulae are keg-only and don't symlink
`llvm-nm` onto `PATH`, so `Command::new("llvm-nm")` fails to spawn (`ENOENT`)
and the loop silently falls through to the same broken `nm`.

Proposed fix (sketch, not applied):
1. Add a shared helper in `tools.rs`, e.g. `pub(crate) fn nm_command() -> std::process::Command`,
   that resolves the tool once: honor an env override
   (`SIMPLE_NM_TOOL`/reuse `SIMPLE_LLVM_NM` if such a knob already exists
   elsewhere in the pipeline — grep before inventing a new name), else try
   `llvm-nm` on `PATH`, else probe common Homebrew keg locations
   (`brew --prefix llvm`/`llvm@<N>` — or just glob
   `/opt/homebrew/opt/llvm*/bin/llvm-nm` and `/usr/local/opt/llvm*/bin/llvm-nm`
   picking the highest version), else fall back to plain `nm`.
2. Replace the 3 raw `Command::new("nm")` construction sites in `stubs.rs`
   (`scan_nm_defined_undefined` at line ~138, and the two inline builds at
   ~523 and ~548) and the `nm_cmd` build at ~572 (the `plat_config.system_scan_libs`
   loop — currently `std::process::Command::new("nm")` with
   `plat_config.nm_flags`) with calls to the new shared helper.
3. Replace the 3 sites in `linker.rs` (`read_global_symbol_types` at line 78,
   plus the two more at 280 and 317 — not yet inspected in this session, same
   pattern expected) similarly.
4. Update `tools.rs::archive_defined_symbols` (line ~323) to use the same
   shared helper instead of its own narrower `["llvm-nm", "nm"]` loop, so
   there is exactly one tool-resolution policy in the codebase.
5. Re-run stage4 native-build after landing and re-diff the stub list — the
   405-symbol "core rt_*" bucket and probably a meaningful slice of buckets
   (a)/(c) should evaporate.

2026-07-11 implementation status: the shared `nm_command()` helper is now
implemented in `tools.rs`, and the raw `Command::new("nm")` users in
`stubs.rs`, `linker.rs`, and `archive_defined_symbols` route through it.
The helper honors `SIMPLE_NM`, prefers the highest-version available
`llvm-nm` across `PATH` and Homebrew LLVM keg paths, and falls back to `nm`.
Focused Rust checks pass:

- `cargo check -p simple-compiler`
- `cargo check -p simple-driver`

This is only the source-level prerequisite. The macOS GPU/backend TODO remains
open until a fresh self-host candidate built with this source passes
`scripts/check/cert/redeploy_gate/redeploy_gate.shs` and post-swap smoke.

### Gate re-run WITH the nm fix (2026-07-11): measured results + NEW blocker — runtime-lane selection

Seed rebuilt (`cargo --profile bootstrap`, script detected staleness itself),
`bootstrap-from-scratch.sh --full-bootstrap --full-cli` run twice; stage2
binary verified to contain the new code (`strings | grep SIMPLE_NM`). One
amendment forced by the gate itself: **PATH-first llvm-nm resolution is
unsafe** — `bootstrap-from-scratch.sh:261` prepends the llvm@18 keg to PATH,
and LLVM 18's reader rejects rustc-1.94's LLVM21-tagged members exactly like
Xcode `nm` (verified: `Unknown attribute kind (102) … Reader: 'LLVM 18.1.8'`,
0 `rt_array_all` found). Hence the highest-`--version` selection in the
landed helper.

| Stage-4 config (stage2-driven, dynload, cranelift) | Stubs |
|---|---|
| Standard gate command (no `--runtime-path`) — pre-fix baseline | 822 |
| Standard gate command — with nm fix | 807/808 |
| + `--runtime-path src/compiler_rust/target/bootstrap`, `SIMPLE_NM=/usr/bin/nm` (broken reader, control) | 1041 |
| + `--runtime-path …/target/bootstrap`, fixed reader | **662** |
| + non-seed stage4 `--runtime-path`, tagged process args, and bootstrap-CLI runtime selection | **808** |

Interpretation:
- **The nm fix works: 1041 → 662 (−379 symbols) when the full archive is in
  the scan**, and a `comm -12` cross-check of the remaining 662 against the
  llvm-nm-22 defined set of `target/bootstrap/deps/libsimple_runtime.a` is
  **empty** — zero archive-resolvable symbols are still being stubbed. The
  measurement bug this doc's Step 1 identified is fully closed.
- **But the standard gate barely moves (822→807/808)** because the script's
  *stage2-driven* stage-4 branch passes **no `--runtime-path`**
  (`bootstrap-from-scratch.sh:692-706`; the seed-driven branch at :676-690
  and stage2/3 DO pass it). Without it,
  `config.rs::resolve_runtime_lane` → CoreCBootstrap →
  `selected_runtime_library` puts the minimal on-the-fly
  `build_core_c_runtime_library()` archive FIRST in the candidate list and
  `candidates.into_iter().next()` selects it, shadowing the complete
  `deps/libsimple_runtime.a` (appended second via `find_runtime_library`).
  The minimal archive genuinely lacks ~700 `rt_*` symbols, so the stub wall
  persists regardless of nm quality. **New ordered-plan item: pass
  `--runtime-path` in the non-seed stage-4 branch (script fix) and/or fix the
  candidate ordering in `selected_runtime_library` (seed fix).**
- Re-audited buckets of the honest 662 (llvm-nm-verified, dump
  `stubs_rtpath.txt` in session scratchpad): gpu/graphics 130,
  cranelift/jit/smf 78, os/hw-specific 73, sqlite 27, http 22, `_dot_` trait
  methods 11, type-descriptors 12, other `rt_*` 207, non-`rt_` misc 102.
  These are the true bucket-(a)/(c) inputs for ordered-plan step 3
  (scan-after-GC).
- **2026-07-11 third-wave update:** the stage2-driven stage4 branch now passes
  `--runtime-path`, `rt_process_run` keeps the args array tagged, and core-C
  runtime selection skips stale bootstrap archives that lack CLI bootstrap
  symbols. Fresh `--full-bootstrap --deploy --no-mcp --jobs=half` rebuilt the
  seed/runtime; stage2 and stage3 passed; stage4 linked and now recognizes
  `-c`/argv with real `rt_get_args`, `rt_cli_get_args`, `rt_array_len`,
  `rt_string_len`, `rt_file_read_text`, and `rt_process_run` symbols. Smoke
  still fails before deploy: `-c 'print(1+1)'` reports
  `error: failed to run -c snippet`, and `run <file>` reports a blank
  `Parse error`. The remaining 808-stub preview includes parser/source
  symbols (`_lexer_tokenize`, `_input_chars`, `_input_trim`, `_chars_len`,
  `_parts_len`, `_path_*`), so the next ordered work is scan-after-GC /
  entry-closure tightening or owner routing for the parser/lexer run path.
- **Smoke matrix: FAIL in both configs — NOT deployed.** 807-build: `check`/
  `test` exit 3 silently, `run` parse-errors (file/lexer externs stubbed).
  662-build: `--version` OK but `run file.spl` and `-c 'print(1+1)'` ignore
  argv and drop into interactive mode (CLI dispatch symbols among the 662,
  e.g. bare `rt_cli`). Deployed `bin/release/aarch64-apple-darwin-macho/simple`
  untouched; backup `simple.jul5.bak` intact.

## Ordered fix plan (superseded for item 1 — see Step 1 status above)

1. ~~**Runtime-archive completeness (highest leverage, ~400+ symbols).**~~
   **SUPERSEDED.** Re-investigation (above) shows the archive was never
   incomplete — this was an `nm`-tool-version measurement artifact. Replace
   this step with: **fix the `nm`-tool resolution in `stubs.rs`/`linker.rs`/
   `tools.rs`** (see "Seed diff status" above), then re-run stage4
   native-build and re-diff the stub list from a clean baseline before
   trusting any of buckets (a)/(b)/(c) in the table above.
   <details><summary>Original (incorrect) step 1 text, kept for history</summary>

   Diagnose why `target/bootstrap/deps/libsimple_runtime.a` (391 T-symbols,
   built 2026-07-10T23:09) is far smaller than `target/debug/deps/libsimple_runtime.a`
   (22,576 T-symbols, built 2026-07-11T00:28) — likely a stale/partial
   bootstrap-lane build, or the bootstrap lane intentionally builds a minimal
   subset and stage4 should instead route through the `simple-core`/
   `core-c-bootstrap` lane with `find_abi_complete_simple_core_runtime_library`
   returning a real hit. Rebuild or reroute so stage4 links the complete
   archive. Re-run stage4 native-build and re-diff the stub count.
   </details>
2. **Fix the bare-vs-`rt_`-prefixed extern mismatch (~22+ symbols, bucket b).**
   `src/lib/nogc_sync_mut/fs.spl:617-639` and the `nogc_async_mut/fs.spl`
   twin: rename externs to their `rt_`-prefixed forms (matching
   `nogc_sync_mut/io/file_ops.spl`'s already-correct wrapper pattern) or
   route through a thin wrapper. Grep the remaining ~55 "misc" bucket for the
   same bare/`rt_` mismatch pattern first — likely more of that ~55 resolves
   the same mechanical way.

   **STATUS (2026-07-11): DONE for both twins, partially resolvable.** Of the
   30 bare externs declared in the block (22 was the doc's original live-stub
   count; `path_join`/`path_normalize`/`path_is_absolute` are unused
   in-module dead declarations not previously counted), verified against
   `src/runtime/runtime.h` **and** `runtime.c`/`runtime_native.c` (several
   real symbols — `rt_file_read_bytes`, `rt_file_write_bytes`,
   `rt_file_move`, `rt_dir_delete`, `rt_dir_walk`, `rt_dir_list` — exist in
   the `.c` sources but are missing from the `runtime.h` header, so both were
   checked):
   - **13 renamed 1:1** (extern decl + in-module call site changed to the
     real `rt_` name): `file_read_text`→`rt_file_read_text`,
     `file_read_bytes`→`rt_file_read_bytes`,
     `file_write_text`→`rt_file_write_text`,
     `file_write_bytes`→`rt_file_write_bytes`,
     `file_append_text`→`rt_file_append_text`, `file_exists`→`rt_file_exists`,
     `file_delete`→`rt_file_delete`, `file_copy`→`rt_file_copy`,
     `file_size`→`rt_file_size`, `dir_create_all`→`rt_dir_create_all`,
     `dir_delete`→`rt_dir_delete`, `dir_exists`→`rt_dir_exists`.
   - **5 thin-wrapped** (real `rt_` symbol exists under a different name or
     signature; old bare name kept as a plain `fn` so in-module call sites
     didn't need to change): `file_rename`→wraps `rt_file_move` (name
     differs), `dir_create`→wraps `rt_dir_create(path, false)` (real symbol
     takes an extra `recursive: bool`), `dir_delete_all`→wraps
     `rt_dir_remove_all` (name differs), `dir_read`→wraps
     `Some(rt_dir_list(path))` (real symbol is non-optional `[text]`),
     `dir_is_empty`→composed as `rt_dir_list(path).len() == 0` (no dedicated
     symbol exists).
   - **9 unresolvable-here, live** (no `rt_` symbol anywhere in the runtime
     sources; a real fix needs new pure-Simple or new runtime implementation,
     out of scope of a naming-mismatch fix): `path_parent`, `path_filename`,
     `path_extension`, `path_stem`, `path_components`, `path_with_extension`,
     `file_metadata` (no struct-returning `rt_` symbol), `walk_dir` (real
     `rt_dir_walk`/`rt_dir_list` only return bare `[text]` paths, not
     `[DirEntry]` — building that needs new per-entry stat logic, not a
     rename), plus `glob_find`/`glob_matches` counted together (no
     `rt_glob_*` symbols exist) = 9 total.
   - **3 unresolvable-here, dead** (also no `rt_` symbol, and additionally
     unreferenced anywhere in-module): `path_join`, `path_normalize`,
     `path_is_absolute`.
   - Verification: `bin/simple check` clean on both files; interpreted-mode
     smoke tests (`SIMPLE_EXECUTION_MODE=interpret`) exercising every
     renamed/wrapped symbol (dir create/list/is_empty/rename/delete, file
     read/write/exists/delete) round-tripped correctly end-to-end.
     `test/01_unit/app/cli_parser_spec.spl` still green (2/2).
   - **Side finding (not fixed here, out of scope):** the 2-arg
     `(text, bool)` extern signature (`rt_dir_create(path, recursive)`)
     produces a wrong/corrupted result under the default JIT execution path
     (`bin/simple run`, no env override) but is correct under
     `SIMPLE_EXECUTION_MODE=interpret` — a pre-existing Cranelift-JIT FFI
     marshalling bug for bool-typed extern args, reproduced with an
     unmodified standalone extern declaration unrelated to this fix's
     renames. Worth a follow-up bug entry; not blocking this step since the
     interpreter path (what stage4/native-build symbol resolution and the
     existing call sites rely on) is correct.
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

## Step 2 status (2026-07-11): DONE — bare fs externs fixed in both variants

30 bare externs in `src/lib/nogc_sync_mut/fs.spl` + `nogc_async_mut` twin audited against
runtime.h/runtime.c/runtime_native.c: **12 renamed 1:1** to the real `rt_*` symbol
(file_read_text/read_bytes/write_text/write_bytes/append_text/exists/delete/copy/size,
dir_create_all/dir_delete/dir_exists); **5 thin-wrapped** where the real symbol differs
(file_rename→rt_file_move, dir_create→rt_dir_create(path,false), dir_delete_all→rt_dir_remove_all,
dir_read→Some(rt_dir_list), dir_is_empty via rt_dir_list().len()==0); **12 unresolvable-here**
(9 live: path_parent/filename/extension/stem/components/with_extension, file_metadata, walk_dir,
glob_find/glob_matches; 3 dead: path_join/normalize/is_absolute) — NO rt_ symbol exists; not
invented; these remain stubs until runtime exports land.

Verified: `bin/simple check` clean both files; cli_parser_spec 2/2; interpreter extern tables cover
every renamed name; interpret-mode smoke round-tripped all renamed/wrapped symbols.

Side findings: (1) `rt_dir_create(text,bool)` returns corrupted result under Cranelift JIT but
correct under interpret — pre-existing JIT FFI marshalling bug for (text,bool) extern args
(follow-up bug candidate). (2) Several rt_ symbols exist in runtime.c/runtime_native.c but are
missing from runtime.h declarations (rt_file_read_bytes/write_bytes/move, rt_dir_delete/walk/list).

## Follow-up status (2026-07-18): walk/glob/lexical-path stubs reduced

`walk_dir`, `glob_find`, `glob_matches`, `path_parent`, `path_filename`,
`path_extension`, `path_stem`, `path_components`, and `path_with_extension` now
stay in pure Simple.
They reuse the existing `rt_dir_walk`, shared `std.glob` matcher, and `std.path`
lexical helpers; no new runtime ABI was added. The core-C `rt_dir_walk` owner now returns the canonical `rt_array_*` /
`rt_string_*` representation consumed by native Simple iteration instead of the
legacy `spl_array_*` representation. The remaining live unresolvable entry is
`file_metadata` (1 total); the three dead path declarations remain separate
cleanup.

Focused evidence: both fs/glob profile twins pass incremental source checking; a
pure Stage2 LLVM matcher probe and a core-C-bootstrap `Glob.matches()` /
`matches_path()` facade probe compile and run successfully. The C runtime focus
contract and source parity spec now assert canonical directory-walk array access.
A focused source/behavior spec now defines Unix/Windows-form and empty-path
`Path.stem`, parent, filename, extension, components, and
extension-replacement coverage;
staged native execution and the full Stage4 gate remain pending.
