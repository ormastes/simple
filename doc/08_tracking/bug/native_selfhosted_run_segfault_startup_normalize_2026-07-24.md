# Deployed native self-hosted `bin/simple` segfaults on every `run`/`test`

- **Date:** 2026-07-24
- **Severity:** high (blocks all `run`/`test` reproduction on the affected
  binaries; discovered as a side-effect while investigating
  `sspec_test_runner_undercounts_it_blocks_2026-07-24.md`)
- **Status:** open (out of scope for the SSpec undercount fix; filed for a
  separate lane)

## Symptom

The deployed native self-hosted binary segfaults on **every** invocation of
`simple run <file.spl>` or `simple test <file.spl>` (via `cli_handle_run` /
`cli_run_file`), even for a trivial `fn main(): print "hello"` script — no
compile error, immediate `SIGSEGV`. `--version`, `lint`, `doc-coverage`, etc.
are unaffected.

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

## Suggested next steps

- Rebuild `bin/simple` fresh via `bin/simple build bootstrap` in a clean
  worktree and check whether the crash is a stale-artifact issue (this
  worktree has substantial unrelated WIP under `src/os/compositor/`,
  `src/os/hosted/`, `src/os/desktop/shell.spl` per `git status` — plausible
  the deployed binary was built from a transiently broken WIP tree) or a
  genuine regression that survives a clean rebuild.
- If it survives a clean rebuild: bisect the `args`/`[text]` value flowing
  into `startup_plan_from_metadata` / `startup_normalize_program_args` for a
  null-vs-empty-array representation bug, likely in `interpret_file` /
  `compiler_driver_run_compile`'s construction of the interpreted program's
  `program_args`.
