# Deployed native self-hosted `bin/simple` segfaults on `run`/`test`/`native-build`

- **Date:** 2026-07-24
- **Severity:** high (blocks `run`/`test` and incremental native builds on the affected
  binaries; discovered as a side-effect while investigating
  `sspec_test_runner_undercounts_it_blocks_2026-07-24.md`)
- **Status:** `run`/`test` source-fixed with redeployment pending;
  `native-build` root unproven

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
