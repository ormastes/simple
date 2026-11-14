# Native `llm_caret workspace attach` cannot start the smux owner: it runs ITSELF as `<exe> run smux_client.spl`

Status: open
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
