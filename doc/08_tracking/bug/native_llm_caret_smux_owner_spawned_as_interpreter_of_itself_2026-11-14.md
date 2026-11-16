# Native `llm_caret workspace attach` cannot start the smux owner: it runs ITSELF as `<exe> run smux_client.spl`

Status: verification-pending (native re-verified 2026-11-15)
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

## Verification run 2026-11-15 (run-only, no rebuild)

Worktree at `9bffbf8ef3a` (PR #9238 fix). Seed `src/compiler_rust/target/bootstrap/simple.exe`
built from that commit; `build/nb/llm_caret.exe` native-built from it. `SIMPLE_BINARY=$SEED`,
`claude` removed from PATH (`command -v claude` empty).

- native `workspace_cli_system_spec.spl` (`LLM_CARET_NATIVE_BIN=build/nb/llm_caret.exe`):
  `Results: 4 total, 3 passed, 1 failed` (exit 1)
- interpreted `workspace_cli_system_spec.spl` on `$SEED` (seed copied over `bin/simple.exe`):
  `Results: 0 total, 0 passed, 0 failed` (exit 5; `SPEC FILE VERDICT: ... timeout=1 reason=child-timeout budget_ms=900000`)
- native `caret_cli_help_system_spec.spl`:
  `Results: 4 total, 4 passed, 0 failed` (exit 0)

Next defect: in native mode, step `attaches three agents, isolates their worktrees,
broadcasts, and tears down` still fails for agent-1/2/3 with
`expected error new_session_failed smux owner did not start to contain window cli-team:agent-N`;
then `session cli-team alive=false`. The native owner still does not come up via
`process_spawn_async`. The interpreted run exceeds the 900 s child budget.
Status stays verification-pending.

## Root cause analysis 2026-11-15

Status stays verification-pending. Run-only lane (no build, host disk ~4 GB free),
worktree branch `work/native-owner-start-20261115` at `8eaed4c6d1b`, binaries reused:
`build/nb/llm_caret.exe` (2026-11-14T22:52:30, 14244864 B) and seed
`src/compiler_rust/target/bootstrap/simple.exe` (2026-11-14T22:42:11). `claude` off PATH.

### Static trace (native caret)

`_smux_owner_up` (`agent_workspace.spl:336`): fast path `list-sessions`; else writes
`<session> <token>` to `%LOCALAPPDATA%/simple/caret_smux/<session>-<hash(repo)>.owner`,
`smux_owner_argv(exe, env SIMPLE_BINARY, <root>/src/app/hosted_apps/smux_client.spl, <file>)`
-> `[SIMPLE_BINARY, run, <client>, --serve-owner-file, <file>]` (native exe base is
`llm_caret.exe`, so `SIMPLE_BINARY` empty => immediate `false`, same error text, no wait).
`SIMPLE_BINARY` is cleared for the spawn and restored after. `start_outliving_process(root, argv)`
runs `process_spawn_async("powershell", ["-NoProfile","-NonInteractive","-Command",
"Start-Process -WindowStyle Hidden -WorkingDirectory '<root>' -FilePath '<SIMPLE_BINARY>'
-ArgumentList '\"run\"','\"<client>\"','\"--serve-owner-file\"','\"<file>\"'"])`
(C `win_process_spawn_async_owned_environment_v1`: no job, NUL std handles,
`CREATE_NO_WINDOW`, inherited env, cwd = caller's) and requires `process_wait(hop, 30000) == 0`.
Readiness: `_smux_req(ws, "list-sessions") != nil` every 500 ms for 240000 ms; the owner
rewrites the file to `<id> <addr> <token> <pid>` once bound.

### Measured

- Standalone `llm_caret.exe workspace rca1 attach agent-1 --repo <fresh repo>`
  (`SIMPLE_BINARY=$SEED`), 04:58:25 -> 04:58:59, rc=0:
  `window rca1:agent-1` / `ok smux: created window id6`. Owner process seen:
  `"...\bootstrap\simple.exe" "run" "C:/dev/wt/sqlcov-20261114/src/app/hosted_apps/smux_client.spl" "--serve-owner-file" "C:/Users/user/AppData/Local/simple/caret_smux/rca1-941330179.owner"`;
  owner file in four-field form `rca1 127.0.0.1:65189 <tok> 22160` within ~34 s. `workspace rca1 kill` -> `ok`, owner gone.
- Native `workspace_cli_system_spec.spl` (`LLM_CARET_NATIVE_BIN=build/nb/llm_caret.exe`,
  `SIMPLE_BINARY=$SEED`, run by `$SEED test`), twice:
  `SPEC FILE VERDICT: ... outcome=OK declared>=4 executed=4 passed=4 failed=0` /
  `Results: 4 total, 4 passed, 0 failed` (first run 05:02:34 -> 05:03:36). During the team
  scenario the owner for `cli-team-947543512.owner` was the seed interpreter, parent chain
  outside any kill-on-close job, and it bound and served all three attaches.

### Conclusion

The spawn path (#9211 argv + #9238 `process_spawn_async` hop) is correct with these
binaries: the owner starts, outlives the hop, binds, and the readiness probe sees it.
The 2026-11-15 `3/4` failure is NOT reproduced with the same binaries. Likely causes of
that run, neither proven: (a) `SIMPLE_BINARY` not reaching the caret (gives the same
`smux owner did not start` text instantly), or (b) owner interpreter start exceeding the
240 s budget under host load (one owner start = full interpreter boot of `smux_client.spl`;
~34 s idle here). Stale owner files from other runs (`cli-team-899123459.owner`,
`cli-team-979861953.owner`, different repo hashes) were present and did not interfere.

### Minimal fix proposal

No code fix is justified by evidence. Proposed diagnostic-only follow-up (not done here):
make `_smux_owner_up` distinguish its three failure exits in the error text
(`SIMPLE_BINARY unset`, `Start-Process hop failed rc=<n>`, `owner not ready after 240 s`)
so the next failing run names its cause.

### Still needed

Native rebuild not required for this conclusion. Close-out needs the unblock condition's
`workspace_recovery` native run, and a re-run of the 3/4 environment if it recurs.

## Owner-start error causes + native recovery run (2026-11-15, lane `work/owner-start-error-causes-20261115`)

Status stays verification-pending. `_smux_owner_up` is now `smux_owner_start(ws, exe) -> text`
and each failure names its cause after the unchanged `smux owner did not start` prefix:
`SIMPLE_BINARY not set (native <exe> needs a simple interpreter)`, `launcher failed`,
`not ready after 240 s`, `owner file setup failed`.
Spec `test/01_unit/app/llm_caret/smux_owner_start_error_spec.spl` (interpreted, seed):
red `function smux_owner_start not found` -> green `Results: 1 total, 1 passed, 0 failed`.

- native `workspace_recovery_system_spec.spl` (`LLM_CARET_NATIVE_BIN=build/nb/llm_caret.exe`,
  existing exe from 2026-11-14 22:52, no rebuild, `SIMPLE_BINARY`=seed):
  `Results: 12 total, 12 passed, 0 failed` (exit 0)

## Native re-verification 2026-11-15 (release/1.0.0 @ cd0630ec257, incl. #9298)

`build/nb/llm_caret.exe` rebuilt with seed `native-build` (`compiled=712 reused=0`
— the incremental cache was NOT reused this run; full rebuild). Run with
`LLM_CARET_NATIVE_BIN` and `SIMPLE_BINARY=<seed>`:

- workspace_cli_system_spec: `Results: 4 total, 4 passed, 0 failed`
- workspace_recovery_system_spec: `Results: 12 total, 12 passed, 0 failed`
- caret_cli_help_system_spec: `Results: 4 total, 4 passed, 0 failed`

Manual, `SIMPLE_BINARY` unset, `llm_caret.exe workspace x attach agent-1` (rc=1):
`error new_session_failed smux owner did not start: SIMPLE_BINARY not set (native llm_caret.exe needs a simple interpreter)`

## Phase-1 seed at tip re-verification (2026-11-15)

- Seed: Rust seed rebuilt cold at `release/1.0.0` tip `5dd7e582c2b`
  (`cargo build --profile bootstrap --bin simple`, clang-cl, LLVM 23.1.1 activation,
  6m03s, no errors). `--version`: `Simple Language v1.0.0-rc.1`.
- Native builds with that seed (llvm-mingw UCRT, `SIMPLE_NATIVE_INCREMENTAL=1`, shared `build/nb/cache`):
  - devhub: `[native-incremental] 0 reused / 300 rebuilt`, 12.3s compile + 19.1s link, 5775 KB
  - llm_caret: `[native-incremental] 0 reused / 712 rebuilt`, 38.9s compile + 18.0s link, 13992 KB
- Specs (sequential, `Anthropic.ClaudeCode` stripped from PATH, `command -v claude` empty):
  - messenger_read_verbs_history_edges: `Results: 8 total, 8 passed, 0 failed`
  - messenger_read_verbs_damaged_store: `Results: 7 total, 7 passed, 0 failed`
  - native_binary_sqlcipher_read: `Results: 2 total, 2 passed, 0 failed`
  - native_binary_sqlcipher_open: `Results: 4 total, 4 passed, 0 failed`
  - workspace_cli_system: `Results: 4 total, 4 passed, 0 failed`
  - workspace_recovery_system: `Results: 12 total, 12 passed, 0 failed`
  - caret_cli_help_system: `Results: 4 total, 4 passed, 0 failed`
- Status unchanged (verification-pending); this is seed-at-tip evidence, not a status move.

## Flake hunt 2026-11-15 (3 sequential native runs)

`LLM_CARET_NATIVE_BIN=/c/dev/wt/sqlcov-20261114/build/nb/llm_caret.exe SIMPLE_BINARY=<seed-tip.exe> seed-tip.exe test test/03_system/app/llm_caret/workspace_cli_system_spec.spl`, base origin/release/1.0.0, Windows host:

- run 1: rc=0, `Results: 4 total, 4 passed, 0 failed`
- run 2: rc=0, `Results: 4 total, 4 passed, 0 failed`
- run 3: rc=0, `Results: 4 total, 4 passed, 0 failed`

The earlier 3/4 "smux owner did not start" did not reproduce in 3 runs, so no #9298 step-named cause text was captured. Status remains verification-pending; the flake stays unexplained (intermittent, or load-dependent).
