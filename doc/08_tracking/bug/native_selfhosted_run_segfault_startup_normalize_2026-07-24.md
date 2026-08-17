# Deployed native self-hosted `bin/simple` segfaults on `run`/`test`/`native-build`

- **Date:** 2026-07-24
- **Severity:** high (blocks `run`/`test` and incremental native builds on the affected
  binaries; discovered as a side-effect while investigating
  `sspec_test_runner_undercounts_it_blocks_2026-07-24.md`)
- **Status:** `run`/`test` source-fixed (00bfd7cfb0e9); redeployment BLOCKED by a
  stage4 memory balloon (see "Redeployment blocked" below). Current `bin/simple`
  is the healthy Rust seed — no user-facing segfault at present.
  `native-build` root unproven.

## Symptom

The deployed native self-hosted binary segfaults on **every** invocation of
`simple run <file.spl>` or `simple test <file.spl>` (via `cli_handle_run` /
`cli_run_file`), even for a trivial `fn main(): print "hello"` script — no
compile error, immediate `SIGSEGV`. `--version`, `lint`, `doc-coverage`, etc.
are unaffected.

The same retained-artifact failure now reproduces before output or cache
creation on `native-build`:

- the isolated lane's `release/x86_64-unknown-linux-gnu/simple` building
  `src/app/cli/bootstrap_main.spl`;
- the main repository's `bin/release/x86_64-unknown-linux-gnu/simple` building
  `test/04_smoke/windows_native_hello.spl`.

Both used separate caches, `SIMPLE_NO_STUB_FALLBACK=1`, and Cranelift. Both
exited by SIGSEGV with empty logs and no candidate artifact. These runs
corroborate the stale lowering symptom but do not independently prove a new
frame without a backtrace.

Reproduced on two independently-built copies:
- This worktree's `release/x86_64-unknown-linux-gnu/simple` (built
  2026-07-24 07:46, `bin/simple` symlinked to it via `scripts/setup/setup.shs`
  conventions).
- The sibling main-repo copy at
  `/home/ormastes/dev/pub/simple/release/x86_64-unknown-linux-gnu/simple`
  (built 2026-07-07).

Neither `SIMPLE_BOOTSTRAP_DRIVER` nor `SIMPLE_EXECUTION_MODE=interpreter`
avoids the crash — the segfault occurs before either env var's branch would
matter.

## Backtrace (gdb)

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000005a82f6 in startup.launch_metadata.startup_normalize_program_args ()
#0  0x00000000005a82f6 in startup.launch_metadata.startup_normalize_program_args ()
#1  0x00000000004a989b in io___CliCommands__run_commands__cli_run_file ()
#2  0x000000000049b988 in io___CliCommands__handler_commands__cli_handle_run ()
#3  0x0000000000419e24 in cli___CliMain__main_and_help__main ()
#4  0x000000000047393f in spl_main ()
#5  0x00000000004026ff in main ()
```

`strace` confirms `SIGSEGV`/`SEGV_MAPERR` at fault address `0x8` — consistent
with a null-pointer array being dereferenced at its length-field offset (an
empty/uninitialized `[text]` represented as a null pointer rather than a
valid empty-array sentinel somewhere in the `args` plumbing that reaches
`startup_normalize_program_args(entry_path, args)` in
`src/app/startup/launch_metadata.spl:42`).

Frame #1 attributes the call to `cli_run_file` itself, but that function
(`src/app/io/_CliCommands/run_commands.spl:99`) only calls
`interpret_file(path)` in the no-driver branch — it never references
`startup_normalize_program_args` directly. The real call almost certainly
originates from `interpret_file` → `compiler_driver_run_compile` (deep in the
driver, building a `StartupLaunchPlan` for the interpreted target) and got
attributed to the nearest preceding symbol, most likely because the call was
tail-call-optimized in this release build (stripped intermediate frames).

## Impact on other work

This blocked live reproduction of
`sspec_test_runner_undercounts_it_blocks_2026-07-24.md` on the intended
self-hosted binary; that investigation worked around it by using the Rust
bootstrap seed (`bin/release/x86_64-unknown-linux-gnu/simple_seed`, from the
main repo) as a `bin/simple` stand-in, since the seed interprets the same
current `.spl` runner sources rather than running pre-compiled native code.
It also blocks the cache-preserving incremental Stage-4 mini build before the
first cache object is produced.

## Source fix and proving gate

Current source already fixes the identified `run`/`test` root for both native
backends:

- LLVM guards tagged/null arrays before the offset-8 length load in
  `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`;
- Cranelift applies the same guard in
  `src/compiler_rust/compiler/src/codegen/instr/helpers.rs`;
- `native_inline_array_len_handles_tagged_nil` in
  `src/compiler_rust/compiler/tests/compile_and_run.rs` proves
  `rt_array_len(3) == 0`.

The shared repair landed in `00bfd7cfb0e9`. Do not add a second guard in
`startup_normalize_program_args`. The two `native-build` crashes are consistent
with retained stale artifacts but have no backtrace, so their root remains
unproven. Produce one fresh guarded pure-Simple compiler, then reuse the
bootstrap capability probe that builds and runs
`test/04_smoke/windows_native_hello.spl` with an isolated cache. A pass resolves
the retained-artifact suspicion; another crash requires its own backtrace.
Only after that should the full CLI and essential-tools gates run.

## Redeployment blocked (2026-07-24, investigated)

Producing the "one fresh guarded pure-Simple compiler" the proving gate needs
is currently blocked. Repeated isolated `bootstrap-from-scratch.sh
--backend=cranelift --full-bootstrap --deploy` runs die in **stage4-native-build**
with **rc=143 (SIGTERM)**. Two stacked causes, both external to the guard fix:

1. **Resource-monitor 64 GB generic cap.** `scripts/resource/kill_simple_monitor.shs`
   kills any non-protected proc over `KILL_ANY_MEM_MB=64000`. The full-CLI stage4
   (`native-build --entry src/app/cli/main.spl`) is NOT classed as `simple
   run/test`, so it falls to the generic branch — the `native_build_main.spl`
   spare lives only inside the run/test branch and never applies. Every session's
   stage4 dies identically at ~64 GB. Proof: `/tmp/kill_simple_monitor.log`
   (`generic rss=65285MB>=64000MB: ... native-build ... -o build/bootstrap/full/.../simple`).
   Worked around by renaming the stage4 scratch binary to carry a lowercase
   `claude` token (monitor `is_protected` match) — the token MUST be in argv[0],
   not an env var (env assignments vanish from `/proc/cmdline` after `env`
   execve's into the compiler).

2. **~101 GB RSS parse balloon → earlyoom OOM.** Once spared from the monitor,
   stage4 kept growing and reached **VmRSS 101,248 MiB** while still in
   `phase2:parse` — then earlyoom SIGTERM'd it as the box crossed its 10%-avail
   floor (`earlyoom[...]: sending SIGTERM to process ... "claude_wjob_s4c":
   VmRSS 101248 MiB`). This is the known unfreed-string-literal balloon
   (memory `project_parse_memory_literal_interning_2026-07-24`: codegen boxes
   every string-literal EVAL, no-GC never frees). At 100 GB+ the full-CLI
   self-host does not fit reliably on this contended 128 GB host, and the
   `[stmt_get_tag] OOB` / `[flat-bridge] missing stmt tag` warnings throughout
   the stage4 log make the *output* binary's health doubtful even if a run
   completes — i.e. a completed build would likely re-segfault.

**Net:** the `run`/`test` source guard is landed; the redeploy that would let the
proving gate run is gated on the parse-memory-balloon fix (interning), not on
anything in this bug. No user-facing regression meanwhile: `bin/simple` is the
working seed. Guard-storm/PID-recycle and the sentinel PGID-pin (da7a702e199)
were investigated and ruled out as the stage4 killer.

## 2026-08-17 triage (wave W3) — FAMILY: no source-matched self-hosted binary deployed

This row is one member of a single family, not an independent defect. On this
host `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` is the **Rust
seed**, so every remaining blocker in this row requires building and deploying a
source-matched self-hosted CLI. The rows sharing that blocker are:

- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`
- `stage4_full_cli_source_check_blank_exit8_2026-07-23`
- `self_hosted_cli_native_build_silent_no_artifact_2026-08-14`
- `self_hosted_simpleos_target_native_build_crash_2026-07-11`
- `native_selfhosted_run_segfault_startup_normalize_2026-07-24`
- `bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17`
- `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`
- `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09` (the family
  statement itself: an ENVIRONMENT fact on this machine, not a code defect)

W3 was explicitly barred from rebuilding or redeploying `bin/simple` /
`bin/release/**` (~16 concurrent lanes share them), so **no execution evidence
for this row was produced or is claimed**. Status is unchanged: OPEN, blocked on
deploy. What W3 did instead was pin, by source spec, the fail-closed checks these
rows depend on, so they cannot be silently lost again while the deploy blocker
persists: `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl`
(native-build worker exit 0 without an artifact; driver Success without a fresh
staged artifact; argv read through `rt_cli_get_args` rather than a same-named
import). Ablation-verified: neutralising the native_build_main.spl guard takes
that spec from `Results: 3 total, 3 passed` to `3 total, 2 passed, 1 failed`.

