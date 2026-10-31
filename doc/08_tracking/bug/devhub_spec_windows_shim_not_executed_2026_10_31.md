# devhub specs: extensionless `#!/bin/sh` fake binaries never run on the Windows seed

Status: OPEN. Date: 2026-10-31. Branch: work/devhub-gh-spec-20261031.

## Symptom

On the Phase 1 seed (Windows, `simple.exe run`), these fail:

- `test/01_unit/app/devhub/cmd_github_spec.spl`: 13 x `expected false to equal true`
  (argv-log `contains` checks), plus 1 x `expected 1 to equal 0`.
- `test/01_unit/app/devhub/cmd_tasks_spec.spl`: 20 x `expected false to equal true`,
  plus 1 x `expected 1 to equal 0` (`jira: --reason has no equivalent ...`, which
  prints `transition failed: acli error:` with an empty message).

Fixed by this change: the `semantic: method contains not found on type nil` failures
(see Cause 1 below).

## Cause 2 (open): the seed cannot launch the fake shims

The specs install fake `gh`/`acli` as `build/test-*-fixture/<name>` with a
`#!/bin/sh` body and prepend that directory to `PATH`. The seed's
`rt_process_run_timeout` (`src/compiler_rust/compiler/src/interpreter_extern/system.rs:802`)
calls `Command::new(resolve_command_path(cmd))`. On win32, `resolve_command_path`
only maps `/bin/sh`, `/bin/bash`, `/bin/env` and returns other names unchanged.
A bare extensionless name is not resolved through `PATH` with `PATHEXT`, and a
shebang script is not executed by `CreateProcess`. The spawn fails and the call
returns `(\"\", \"\", -1)`.

Evidence (probe `build/probe_env.spl`, seed `simple.exe`):

- `rt_process_run_timeout("fakegh_probe", ...)` with a `#!/bin/sh` file first on PATH:
  rc=-1, empty output.
- `rt_process_run_timeout("fakegh_probe.cmd", ...)` with a one-line `.cmd` trampoline
  (`sh "%~dp0fakegh_probe" %*`) in the same directory: rc=0, output `FAKE x`.
- `rt_env_set("PATH", ...)` and `rt_env_get("PATH")` round-trip correctly.

Because the shim never runs, the argv log is never written, so every
`log.contains(...)` is false. The `expected 1 to equal 0` cases are the same
failure: the fake is missing, so the command exits non-zero.

**Hazard:** when the fake does not run, PATH falls through to the real `gh`.
The baseline run (before this fix) reached the real GitHub CLI. Its output
included `GraphQL: Could not resolve to a Repository with the name 'owner/name'`
and `no pull requests found for branch "work/devhub-gh-spec-20261031"`. Those
are real `gh` errors, so network calls were made. Later runs excluded the
`GitHub CLI` directory from PATH (see `build/run_spec_nogh.sh`).

## Cause 1 (fixed): nil from `rt_file_read_text`

The seed returns `Value::Nil` for a missing file
(`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:622`). The specs
declared `extern fn rt_file_read_text(path: text) -> text`, which hides that nil.
The fix declares the extern `-> text?` and reads with `?? ""`, in both
`cmd_github_spec.spl` and `cmd_tasks_spec.spl`. Expected values are unchanged.

## Unblock condition

Either:

1. The seed's process launch resolves a bare command through `PATH` plus
   `PATHEXT` on win32, and runs shebang scripts through `sh` when present (seed
   change, `system.rs`), or
2. The devhub specs write `.cmd` trampolines on win32 (test-harness change).

Option 1 is the owner fix, because the same limit affects any spec that uses a
shebang shim on Windows. It is out of scope for this branch.
