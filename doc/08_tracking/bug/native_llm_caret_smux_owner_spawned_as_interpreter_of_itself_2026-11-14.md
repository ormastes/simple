# Native `llm_caret workspace attach` cannot start the smux owner: it runs ITSELF as `<exe> run smux_client.spl`

Status: fix landed, verification-pending (native rebuild required)
Severity: P2 (native-only; workspace panes unusable from a standalone native caret on the smux backend)
Found: 2026-11-14, lane `work/caret-native-defects-20261114`
Seed: built from this branch (import_loader alias fix on `4118fda1a3e`)
Host: Windows 11, llvm-mingw 20260922 UCRT

## Symptom

With the `invalid_name` miscompile fixed
(`native_text_to_bytes_for_loop_reads_packed_words_when_agent_workspace_linked_2026-11-14.md`),
native `llm_caret.exe workspace <id> attach agent-1 --repo <repo>` creates the
worktree, then blocks for the full 240 s owner wait and fails. `status`
afterwards reports `session <id> alive=false`; `kill` reports
`error kill_server_failed <id>`.

`test/03_system/app/llm_caret/workspace_cli_system_spec.spl` with
`LLM_CARET_NATIVE_BIN`: `Results: 4 total, 3 passed, 1 failed` (the team
scenario). Interpreted: 4/4.

## Cause (source design, not a miscompile)

`_smux_owner_up` (`src/app/llm_caret/agent_workspace.spl:314`) starts the owner
as

```
<cli_current_exe_path()> run <root>/src/app/hosted_apps/smux_client.spl --serve-owner-file <path>
```

Interpreted, the current exe is the `simple` binary, so this starts an
interpreter. In a native build the current exe is `llm_caret.exe`, which has no
`run` verb and no `--serve-owner-file` option, so no owner ever listens.

## Decision needed (owner)

Either the native caret serves the owner in-process (link `smux_client`'s
owner entry and add a `--serve-owner-file` verb), or it resolves a `simple`
interpreter explicitly instead of `cli_current_exe_path()`. Not chosen here.

## Unblock condition

Native `workspace_cli_system_spec.spl` 4/4 and `workspace_recovery` green with
`LLM_CARET_NATIVE_BIN` set.

## Fix (2026-11-14)

`smux_owner_argv` (`src/app/llm_caret/pane_backend.spl`) is a pure function choosing the owner argv: the own exe when it is `simple`/`simple.exe`, otherwise the interpreter from `SIMPLE_BINARY`, otherwise an explicit error (no self-exec). `_smux_owner_up` calls it. Spec: `test/01_unit/app/llm_caret/smux_owner_argv_spec.spl` (red 0/4 -> green 4/4). Native `workspace_cli_system_spec.spl` with `LLM_CARET_NATIVE_BIN` is unverified until a native rebuild; a native caret now needs `SIMPLE_BINARY` set to a simple interpreter.

## Native measurements after the fix (2026-11-14, lane `work/caret-native-smux-owner-20261114`)

Status stays verification-pending: correcting the owner command line is
necessary but not sufficient. Two further native defects were measured with a
native `llm_caret.exe` (seed `4118fda1a3e`, llvm-mingw 20260922 UCRT) while
trying the other design (native caret serving the owner through its own
`--serve-owner-file` verb). The first one applies to ANY owner a native caret
starts, including the interpreter owner chosen by `smux_owner_argv`.

1. **A native process cannot start a process that outlives the call.** The
   native C runtime runs every `process_run*` child in a job object with
   `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` and no breakaway
   (`src/runtime/runtime_process.c:561-612` and `:1085-1122`,
   `src/runtime/runtime_process_owned.c:5964-6029`). `_smux_owner_up` starts the
   owner with `powershell Start-Process`; the owner inherits that job and is
   killed when PowerShell returns. Measured with a handle-holding watcher:
   owner `"...\llm_caret.exe" "--serve-owner-file" "<owner file>"` started
   0.9 s after the client, exited after 47 ms with code `0x1`, owner file still
   in its two-field form. The byte-identical `Start-Process` command issued
   from bash leaves the owner serving and the file in its four-field
   `<id> <addr> <token> <pid>` form. Reproduced with a 12-line native probe that
   only calls `process_run_timeout("powershell", [... Start-Process ...])`
   (no `env_set`, hand-written owner file): owner file stays two-field. A
   `Start-Process -Wait cmd /c set` from the same probe does run, and its
   environment matches the bash-parent one, so the cause is the job, not the
   environment or argument quoting. Result seen by the spec:
   `error new_session_failed smux owner did not start` after the 240 s wait.
2. **A natively linked owner cannot open a pane.** With an owner started by
   hand, `workspace attach` reaches it and the owner dies with
   `fatal: called unresolved symbol rt_pty_open (stubbed for link only)`.
   `rt_pty_open`, `rt_pty_spawn`, `rt_pty_read`, `rt_pty_write`, `rt_pty_close`
   are listed in `build/nb/llm_caret.exe.stubbed_symbols.txt`. This blocks the
   in-process-owner design only; an interpreter owner is not affected.

Native `workspace_cli_system_spec.spl` with the in-process-owner build:
`Results: 4 total, 3 passed, 1 failed` (unchanged from before). The landed
`smux_owner_argv` build could not be natively rebuilt in this lane: the seed
fails to parse `src/os/apps/smux/runtime_primary_control_service_v4.spl:131:41`
(`else: current.input_attempts[index] = attempt`, "expected expression, found
Assign"), so its native result is still unmeasured; defect 1 predicts the same
`smux owner did not start`.

Also observed, not investigated: interpreted `workspace <id> kill` after one
`detach` returned `error kill_server_failed <id>` (exit 1) with `bin/simple.exe`
build `89a789ba3ab`, and interpreted `workspace_cli_system_spec.spl` was
`Results: 4 total, 3 passed, 1 failed` twice at `62c3e3f283b` plus the
in-process-owner change (attach, status, broadcast, wait, capture, detach all
exit 0 when replayed by hand). No baseline run without that change was taken.

Note on `smux_owner_argv`: it treats only `simple`/`simple.exe` as an
interpreter. An interpreter under another file name (for example a seed copy
`seed_fix.exe`) with `SIMPLE_BINARY` unset now gets the explicit error where it
previously started the owner.

## Defect 1 fix (2026-11-14, lane `work/native-detached-owner-20261114`)

Status stays verification-pending.

Why it worked interpreted: the interpreter's `rt_process_run_timeout`
(`src/compiler_rust/compiler/src/interpreter_extern/system.rs`) spawns with
plain `std::process::Command` and no job on Windows, so the `Start-Process`
grandchild survives. The native C runtime's bounded run uses a kill-on-close
job. The C `rt_process_spawn_async` (`runtime_process.c`,
`win_process_spawn_async_owned_environment_v1`) uses no job, `CREATE_NO_WINDOW`
and NUL std handles.

Fix (no runtime change, no new extern): `start_outliving_process`
(`src/app/llm_caret/pane_backend.spl`) issues the same PowerShell
`Start-Process` hop through `process_spawn_async` + `process_wait` instead of
`process_run_timeout`; `_smux_owner_up` calls it. Kill-on-close for
`process_run*` children is untouched; POSIX is untouched (the launcher is
Windows-only).

Spec `test/01_unit/app/llm_caret/outliving_process_spec.spl`, built as a native
executable (`native-build <spec> -o x.exe`; `test --mode=native` on the seed
reports "Ran on the interpreter" and is not a native measurement):

- before: `finishes its work after the launching call has returned fail` /
  `1 examples, 1 failures`
- after: `... pass` / `1 examples, 0 failures`
- interpreted (seed at `cda4d2d059a` + this change): `Results: 1 total, 1 passed, 0 failed`

Also fixed here: the seed parser rejected `else: xs[i] = v` after an inline
`if c: <call>` (the `runtime_primary_control_service_v4.spl:131` failure that
blocked the native caret rebuild); `build/nb/llm_caret.exe` now builds.

NOT measured in this lane (free disk fell under the lane floor, 9.8 GB, before
the system specs could run): native and interpreted
`workspace_cli_system_spec.spl`, native `caret_cli_help_system_spec`. The
unblock condition above is therefore still open. A native caret still needs
`SIMPLE_BINARY` pointing at a simple interpreter.
