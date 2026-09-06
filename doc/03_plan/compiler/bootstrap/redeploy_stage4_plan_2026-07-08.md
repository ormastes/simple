# Stage4 Self-Host Redeploy (#79) — Plan (updated 2026-07-11)

## STATUS NOW (2026-07-11, third wave): runtime-path + argv/runtime selection landed locally; stage4 links, smoke still fails in parser path, NOT deployed

The second-wave ordered item (pass `--runtime-path` in the non-seed stage-4
branch and stop selecting stale bootstrap `deps/libsimple_runtime.a` when it
lacks CLI bootstrap symbols) is implemented locally:

- `scripts/bootstrap/bootstrap-from-scratch.sh` now passes
  `--runtime-path "$(pwd)/src/compiler_rust/target/bootstrap"` in the
  stage2-driven stage-4 branch.
- `config.rs::selected_runtime_library` skips runtime-path core-C archives
  that do not expose the bootstrap CLI ABI (`rt_get_args`,
  `rt_cli_get_args`, array/string/file/process basics) and falls back to a
  generated core-C runtime archive only when a core-C runtime archive was
  present but incomplete, or no runtime path was supplied.
- `calls.rs::expand_process_c_runtime_args` keeps the args array tagged for
  `rt_process_run`; masking the low tag bits made delegated self-exec lose
  argv and fall into the REPL.

Verification run:

- `cargo check -p simple-compiler`: PASS.
- `cargo test -p simple-compiler --lib runtime_bundle_auto -- --nocapture --test-threads=1`: PASS, 5 tests.
- `timeout 1800 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy --no-mcp --jobs=half`: FAIL before deploy.
  The script rebuilt the Rust seed/runtime, stage2 and stage3 succeeded, and
  stage4 linked `build/bootstrap/full/aarch64-apple-darwin/simple`.

New blocker:

- Stage4 now recognizes argv and has real linked definitions for
  `rt_get_args`, `rt_cli_get_args`, `rt_array_len`, `rt_string_len`,
  `rt_file_read_text`, and `rt_process_run`.
- `build/bootstrap/full/aarch64-apple-darwin/simple -c 'print(1+1)'` now
  exits with `error: failed to run -c snippet` instead of entering the REPL.
- `build/bootstrap/full/aarch64-apple-darwin/simple run <file>` fails with a
  blank `Parse error`.
- Stage4 still generates 808 stubs. The current preview includes parser/front
  end and source-processing symbols such as `_lexer_tokenize`, `_input_chars`,
  `_input_trim`, `_chars_len`, `_parts_len`, and `_path_*`. The next fix is
  scan-after-GC/entry-closure tightening or owner-function routing so the CLI
  run path does not rely on parser/lexer stubs.

Deploy was not performed; TODO 119 remains open.

## STATUS NOW (2026-07-11, second wave): nm-fix seed landed + gate re-run — smoke STILL FAILS, NOT deployed; blocker re-diagnosed to runtime-lane selection

The proposed `nm_command()` seed fix from
`stage4_stub_symbol_plan_2026-07-11.md` § "Step 1 status" was **applied**
(user-authorized): shared helper in
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` (resolution:
`SIMPLE_NM` env → highest-LLVM-major-version `llvm-nm` among PATH +
Homebrew kegs, probed via `--version` — NOT PATH-first, because
`bootstrap-from-scratch.sh:261` prepends the llvm@18 keg to PATH and LLVM 18's
reader also rejects rustc-1.94's LLVM21-tagged archive members → plain `nm`
fallback; cached in a `OnceLock`), used at all 7 `nm` call sites
(`stubs.rs` ×4, `linker.rs` ×3) + `tools.rs::archive_defined_symbols`.
Seed rebuilt (`--profile bootstrap`), gate re-run twice.

Results (all measured, staged binary `build/bootstrap/full/aarch64-apple-darwin/simple`):

- **Standard gate (`--full-bootstrap --full-cli`): 822 → 807/808 stubs.**
  NOT the drastic drop — because the stage2-driven stage-4 branch of the
  script passes **no `--runtime-path`**, so `config.rs::resolve_runtime_lane`
  falls to the CoreCBootstrap lane and `selected_runtime_library` links the
  **minimal built-on-the-fly core-C archive**
  (`build_core_c_runtime_library`), which genuinely lacks ~700 `rt_*`
  symbols. The full `target/bootstrap/deps/libsimple_runtime.a` is appended
  as a *second* candidate and never chosen (`candidates.into_iter().next()`).
  In this lane the nm fix has almost nothing to resolve against.
- **Same stage-4 command + `--runtime-path src/compiler_rust/target/bootstrap`
  (matching what the script's stage2/3 and seed-stage4 branches already do):**
  broken reader (`SIMPLE_NM=/usr/bin/nm`) → **1041** stubs; fixed reader →
  **662** stubs (62 MB binary). **The nm fix resolves 379 symbols** in this
  config, and **0 of the remaining 662 are defined in the full archive**
  (verified via llvm-nm 22 `comm -12` cross-check) — the measurement bug is
  fully fixed; the remaining 662 are genuinely-undefined (over-linking /
  unimplemented buckets: gpu 130, jit/smf 78, os-hw 73, sqlite 27, http 22,
  `_dot_` 11, type-desc 12, misc rt_ 207, non-rt misc 102).
- **Smoke matrix: FAIL in both configs.** Standard-gate binary: b/c exit 3
  silent, d/e `Parse error` (lexer/file externs stubbed). `--runtime-path`
  binary: `--version` OK but `run file.spl` and `-c` drop into interactive
  mode ignoring argv (CLI dispatch symbols still in the 662).
- **Deploy NOT performed** (gate held). `bin/release/aarch64-apple-darwin-macho/simple`
  untouched (19,783,456 bytes, Jul 5); `bin/simple` symlink intact; backup
  still at scratchpad `simple.jul5.bak` (size-verified).
- **Next work items (ordered):** (1) make the stage2-driven stage-4 branch
  pass `--runtime-path` (or fix `selected_runtime_library` candidate order)
  so the full archive is linked — mechanical, −146 stubs and all
  archive-resolvable symbols; (2) the scan-after-GC / entry-closure
  tightening from the stub plan doc for the remaining ~662, which now have
  trustworthy llvm-nm-verified counts; commit the nm seed fix after peer
  review.

## STATUS NOW (2026-07-11, first wave): redeploy gate wave RUN — smoke matrix FAILED, NOT deployed

User authorized the redeploy; the gate wave was executed and the gate held.

- Pipeline: `scripts/bootstrap/bootstrap-from-scratch.sh --full-cli` (no
  `--deploy`; dynload mode, cranelift stage2/3/4, seed reused). Stage 2 OK,
  Stage 3 self-host OK (hashes differ from stage 2 as expected — embedded
  runtime), Stage 4 linked
  `build/bootstrap/full/aarch64-apple-darwin/simple` (54,080,072 bytes) in
  139.6s (1193 modules compiled, 0 failed).
- **BUT the stage-4 link stubbed 822 unresolved symbols**
  (`SIMPLE_STUB_MISSING_RT=1`), including core runtime:
  `file_read_text`, `file_write_text`, `file_read_bytes`, `dir_read`,
  `lexer_tokenize`, `panic`, `json_serialize`, `path_*`, plus
  `_dot_`-mangled trait methods and `rt_arm_virtio_*`. Full list preview in
  `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`.
- **Smoke matrix on the staged binary (gate criteria): FAIL.**
  - a `--version` → PASS (`Simple v1.0.0-beta`).
  - b `check src/app/cli/bootstrap_main.spl` → FAIL (exit 3, zero output).
  - c both CLI specs → FAIL (exit 3, zero output — cannot read test files).
  - d `run` hello script → FAIL (exit 1, `Parse error in :` — empty
    filename: `file_read_text` is a stub, so every source read returns
    nothing).
  - e nested-replace oracle → FAIL (same `Parse error in :`).
  - f `build bootstrap` re-verify → not attempted (pointless after b–e).
  - `-c 'print(1+1)'` → `error: failed to run -c snippet` — this is also why
    the wrapper script itself died silently at its own built-in smoke
    (`set -e` + failing command substitution at the `stage4_smoke` line).
- **Deploy NOT performed.** `bin/release/aarch64-apple-darwin-macho/simple`
  is untouched (19,783,456 bytes, Jul 5 14:16); `bin/simple` symlink intact
  and working. Backup taken anyway (scratchpad `simple.jul5.bak`,
  size-verified).
- **Conclusion:** the 3-stage minimal-driver bootstrap is VERIFIED, but the
  stage-4 *full CLI* produced by the stage-2 dynload native-build is not
  deployable — the 822-symbol stub wall (same wall as the Jul-10 peer
  retries: `simple.stubdump`, `stage4-stub-symbols.txt` in the logs dir) is
  the actual redeploy blocker. Next work item: resolve the unresolved-symbol
  classes in stage-4 native-build (trait `_dot_` mangling, runtime `file_*`
  externs) so the full CLI links closed, then re-run this exact gate.


> Full dated archaeology of the fix arc (SIGSEGV → DataLayout → verifier
> errors → object emission) moved to
> `redeploy_stage4_plan_history_2026-07.md`. This file is the current status
> and the forward plan only.

## Goal

`bin/simple build bootstrap` (or the equivalent stage2 self-compile) produces a
working self-hosted `simple` binary from current `src/`, gateable and
redeployable to `bin/release/<triple>/simple`.

## STATUS NOW (as of origin `06facdc1`)

Stage 1 of `bin/simple build bootstrap` runs the **llvm-lib AOT / LLVM-C-API**
path (`src/compiler/70.backend/backend/llvm_lib_*`, native-build LLVM-IR
generation run **interpreted** by the deployed `bin/simple`). As of
`06facdc1`:

- **All crash classes are eliminated.** No SIGSEGV, no SIGABRT, no dropped
  calls, no verifier errors. IR generation, verification, and object emission
  all succeed — `object.app.cli.bootstrap_main.o` is written as a valid
  `Mach-O 64-bit object arm64` on this host.
- **The `replace` semantic wall is FIXED (2026-07-10, uncommitted in WC).**
  It was NOT a compiler-source semantic bug: the deployed (Jul-5) `bin/simple`
  worker binary's *nested/chained-call* method dispatcher predates the seed
  fix `050209d9b3` (2026-07-07) that added `replace`/`replace_first` to the
  chained-call str table, so any `X.method(..).replace(..)` chain in
  val/return/expr-statement/tail position aborted the interpreted worker. The
  executed site was `cache_validator.spl:182` (`source_to_cache_path`),
  reached right after native linking succeeds (output_format=both SMF-cache
  step). Fix = mechanical receiver hoists (per the documented "chained
  methods broken — use intermediate var" runtime limitation) at that site +
  the same-family chains on the SMF/SHB/MIR-cache path (smf_manifest,
  watcher_protocol, shb_cache, both incremental.spl twins,
  mir_interp_intrinsics str_replace) + a trace-only `Module.path` crash fix
  in module_lowering.spl. The dispatcher-table fix itself is already on main
  (Rust seed) and becomes live at the next redeploy. Full detail in the bug
  doc's 2026-07-10 semantic-replace section.
- **Determinism MISMATCH FIXED (2026-07-10, uncommitted in WC) —
  `bin/simple build bootstrap` now prints Bootstrap VERIFIED end-to-end:**
  ```
  Stage 1: OK (35576 bytes, hash=11a9c3ca…b293250)
  Stage 2: OK (35576 bytes, hash=11a9c3ca…b293250)
  Stage 3: OK (35576 bytes, hash=11a9c3ca…b293250)
  Bootstrap VERIFIED: All 3 stages produce identical output
  Bootstrap deployed: bootstrap/stage3/aarch64-apple-darwin-macho/simple
  ```
  Two root causes, both fixed at the source (deterministic output, not a
  weakened comparison): (1) `translate_module_to_llvm`
  (`llvm_lib_translate.spl`) iterated `mir_module.functions.values()` — a
  random-seeded `Dict` — so LLVM global/string-constant emission order (and
  therefore `__cstring` layout, section offsets, unwind info, and the code
  signature) varied per process; now both passes run in sorted-function-name
  order. (2) ld64's LC_UUID varies per link; an earlier attempt passed
  `-no_uuid` in the macOS link paths to normalize that metadata, but a later
  full-bootstrap run on 2026-07-10 proved current macOS dyld rejects the
  resulting Stage 2 executable with `missing LC_UUID load command` before
  Stage 3 can run. The linker now keeps LC_UUID for launchability; future
  deterministic-bootstrap work must normalize or compare UUIDs outside the
  deployed executable rather than suppressing the load command. Full diff
  classification in the bug doc's 2026-07-10 determinism section. NOTE: the
  build's final step copies stage3 only into
  `bootstrap/stage3/<triple>/simple`; `bin/release` is untouched — redeploy
  there is still gated on the extended smoke matrix (§ "Re-gate + redeploy
  criteria" below).
- Deployed `bin/simple` (unchanged) still works as a tool in the meantime.

## WHAT LANDED (fix arc, oldest → newest, all on origin/main)

| Commit | One-liner |
|---|---|
| `bfd98b03` (#130) | Stop wiping call/method args under `SIMPLE_BOOTSTRAP` — first ICmp SIGSEGV instance fixed, wall moved to a DataLayout abort (134). |
| `d16a8883` (#133) | Lower function params under `SIMPLE_BOOTSTRAP` — DataLayout wall fixed, wall moved back to exit 139 (ICmp SIGSEGV, different site). |
| `9d11e852` | Declare `rt_cli_get_args` extern (real fix for a dropped call, but crash-report comparison proved it was independent of the fatal 139 — wall re-diagnosed). |
| `9bea509a` | Eliminate use-before-def MIR locals (`lower_if`/`lower_method_call` merge placeholders) + map builtin `print`→`rt_println` — **Stage-1 SIGSEGV (139) eliminated**, now a clean error (exit 1). |
| `f3fb1ed3` | Print LLVM verifier's specific failures on refuse-to-emit + i64 placeholder temps — itemized the Stage-1 wall into a concrete list (19 verifier errors, 6 classes). |
| `2c15339a` | Array→ptr type mapping fix (dominant verifier-error class), correct LLVM kind constants, ret/binop coercion, null-operand diagnostics — verifier errors 19→1. |
| `2f396589` | Match/switch merge-placeholder gap (same class as `9bea509a`'s `lower_if` fix, missed in `lower_match`) + null-guards on remaining translator paths (If-cond, call_indirect/intrinsic args). |
| `ff834dab` | NUL-terminate `LLVMBuildCall2`'s `Name` arg — empty `text.ptr()` is a dangling sentinel in this runtime, was segfaulting `strlen` inside LLVM's C API. **Stage-1 SIGSEGV eliminated for good.** |
| `d80fdadd` | `Ret` with an unmapped operand was building a zero-operand `ReturnInst` (silent verifier mismatch) — now synthesizes a typed placeholder + names the diagnostic. **Verifier now clean.** Wall moved to object emission. |
| `06facdc1` | Triple-aware `Host` CPU selection (was hardcoding `x86-64` for `Host` even on aarch64 — LLVM rejected it and fell back to a garbage subtarget) + format-aware object-magic check (was ELF-only, rejected valid Mach-O). **Object emission SUCCEEDS** (valid Mach-O arm64). Wall moves to the current semantic `replace` error. |

Full per-fix diagnostic detail (probes, crash reports, budget accounting):
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`.

## NEXT STEPS (in order)

0. **822-symbol stub-wall classification + fix plan (2026-07-11, pure
   analysis, uncommitted):** full bucket inventory + root-cause + fix-locus
   table for the stage4 stub wall is in
   `stage4_stub_symbol_plan_2026-07-11.md`. Highest-leverage single fix
   (measured, not inferred): stage4 links the stale 391-symbol
   `target/bootstrap/deps/libsimple_runtime.a` instead of the complete
   22,576-symbol `target/debug/deps/libsimple_runtime.a` — this alone
   accounts for ~400 of the 822/1052 stubbed symbols.
1. ~~Semantic wall (`replace` in nested call context)~~ **DONE 2026-07-10**
   (uncommitted in WC — receiver hoists on the post-link SMF-cache path; see
   STATUS NOW and the bug doc's 2026-07-10 semantic-replace section).
2. ~~Stage-2 determinism MISMATCH~~ **PARTIAL 2026-07-10** — sorted-name
   function emission fixed the string-pool/section-layout nondeterminism. The
   attempted ld64 `-no_uuid` normalization produced byte-stable files but is
   not deployable on this host because dyld rejects Mach-O executables missing
   `LC_UUID`; `_LinkerWrapper/native_linking.spl` now keeps LC_UUID. Treat
   byte-for-byte bootstrap determinism as reopened until UUID handling is solved
   without creating an unloadable executable.
3. **Reconcile the two emit paths.** The original plan (2026-07-08) framed
   path 2 (llvm-lib AOT) as "long-horizon" and path 1 (cranelift/llc
   `SIMPLE_BOOTSTRAP`) as "the realistic route." That framing is now stale:
   path 2 is the path `bin/simple build bootstrap`'s Stage 1 actually runs,
   and it has advanced all the way through IR-gen, verification, and object
   emission to a late-stage semantic error. Path 1's string-literal-drop
   investigation (preserved in the history appendix) is now the
   deprioritized path — do not resume it unless path 2 hits a dead end.
4. **Re-gate + redeploy criteria.** Once Stage 1 (path 2) passes end-to-end:
   run the full `bin/simple build bootstrap` 3-stage (not just Stage 1 in
   isolation) and the extended smoke matrix before any redeploy to
   `bin/release/<triple>/simple`. Do not redeploy on a Stage-1-only pass.

## STANDING TRAPS

- **Peer WC-sweeps re-reverting fixes.** A concurrent full-WC sync from
  another session can silently revert uncommitted edits within seconds.
  Re-verify these sentry sites after any sync or `workspace update-stale`
  before trusting the tree:
  - `llvm_lib_translate_expr.spl:504` / `:506` — `get_value(value_map,
    local.id)` (not raw `local`).
  - All 3 `llvm_types.spl` copies — `LLVMSetDataLayout`'s `layout` arg via
    `(layout + "\0").ptr()`.
  - All 4 `LLVMBuildCall2` call sites — `Name` arg via `(name + "\0")`.
  - `llvm_lib_translate.spl`'s 3 named `Ret`-case diagnostics/placeholders.
  - `llvm_target.spl`'s `for_target_portable_numeric_with_mode` — `Host` has
    its own arm calling `detect_host_arch()`, not grouped with `X86_64`.
- **Stale-WC backup drill.** Before running `jj workspace update-stale` (or
  any operation that can discard uncommitted edits), back up edited files to
  the scratchpad first, then re-verify content after.
- **ONE bootstrap at a time.** `pgrep` for a concurrent `native-build`/`build
  bootstrap` before starting a diagnostic run — each run takes ~400s and two
  overlapping runs corrupt each other's evidence.
- **Duplicate module files.** Numbered (`50.mir`, `70.backend`) vs
  non-numbered (`mir`, `backend`) directories both exist; the seed resolves
  an import to one copy, and instrumentation on the other silently never
  fires. Same for `nogc_sync_mut` vs `nogc_async_mut` `sffi`/`ffi` copies —
  `use std.sffi.llvm.*` resolves to the `nogc_async_mut` copy first
  (resolver order), so `nogc_sync_mut/sffi` is a dead copy for that import
  path. Verify which copy is live before trusting a probe's silence.
- **`(s + "\0").ptr()` rule for C strings.** This runtime's `text.ptr()` on
  an empty or non-NUL-terminated string can return a dangling/non-strlen-safe
  pointer. Any text handed to an LLVM C API (or other extern) that internally
  `strlen`s it must be NUL-terminated explicitly via `(s + "\0").ptr()` —
  this was the root cause of two separate SIGSEGVs in this arc
  (`LLVMSetDataLayout`, `LLVMBuildCall2`).

## Reference

- Bug doc (full diagnostic history, crash reports, budget accounting):
  `doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
- Historical dated sections from this plan (verbatim, oldest → newest):
  `redeploy_stage4_plan_history_2026-07.md`
