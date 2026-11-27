# Caret system specs that stay RED on the Windows host

Date: 2026-10-31
Status: OPEN
Host: Windows 11, `build/caret/seed-fixed.exe` (Rust seed); no self-hosted binary, no tmux.
Specs: `test/03_system/app/llm_caret/`, verdicts measured on `work/release-caret-cmux-20261031`.

## Declined by owner

`feature/llm_caret_cli_hardening_spec.spl` (1/3 pass): lines 274 and 293 require
`bin/caret` to honour `SIMPLE_CARET_NATIVE`. The thin launcher is the owner's
decision: `doc/08_tracking/bug/bin_caret_dropped_native_only_launcher_policy_2026-09-06.md`.
Unblock: only if the owner reverses that decision, or retires these examples.

## Environment prerequisites

Checker stdout names the prerequisite, but these specs assert the exit code first,
so the failure reads as a bare `expected 1 to equal 0`.

| spec | named prerequisite | unblock |
|---|---|---|
| `feature/llm_caret_cli_cached` (0/3), `feature/llm_caret_cli_hidden_cached` (0/5) | `failure_reason=host_target_undetermined`, then no artifact | Windows mapping in the checker `uname` cases (`check-llm-caret-cli-cached.shs:54-59`, hidden twin) AND a cached caret artifact; its candidates (`:88-90`) have no `.exe` form and none exists here |
| `feature/llm_caret_native_closure` (0/2) | `failure_reason=simple_core_archive_not_supplied` | qualified self-hosted runtime (Stage 4) |
| `feature/llm_caret_tui_pty` (0/10) | `failure_reason=script_utility_missing` | `script(1)`, absent from Git for Windows |
| `feature/llm_caret_installed_claude_cli` (0/6) | `failure_reason=pgrep_utility_missing` | `pgrep`, absent from Git for Windows |
| `feature/llm_caret_messaging_phase_cli` (0/3) | `build/bootstrap/{stage3,full}/x86_64-unknown-linux-gnu/simple` (`:121,127`) | Linux host with Phase 3/4 output |
| `caret_slang_local_hello_system` (1/3) | `no model root: pass --models DIR or set SLANG_MODEL_ROOT` | local model root |
| `workspace_cli_system` (2/4), `workspace_recovery_system` (3/7) | `tmux_available()` false | tmux; the spec header scopes it to Unix |

## Real product gap, no spec of its own

`sh bin/caret caret-wrapper-marker --plain` on Windows exits 1 with
`panic: SOSIX ordinary UTF-8 host text provider unavailable: windows`.
Source of the refusal: `src/lib/nogc_async_mut/sosix/text_boundary.spl:60`, which admits only
Unix platforms. `--help` still exits 0. The caller on the caret path was not located.
Unblock: a Windows SOSIX text provider, or a caret path that does not need one.

## Seed bugs (src/compiler_rust not edited)

1. `rt_process_exists` answers true for every PID on non-Unix:
   `compiler/src/interpreter_extern/file_io.rs:3558-3560`. Repro: `rt_process_exists(999983)`
   is true on Windows. `process_ops.spl` guards it with a `tasklist` check until this is fixed.
2. A positioned read fails on Windows: `file_read_text_at("bin/caret", 0, 2)` returns
   `positioned read failed: native status -38`. The provider was not traced.

## cs_live_agents_system: first-run state, budget

With `--timeout 560` Claude and Codex both launched in a real ConPTY pane, then failed;
Kimi never ran because the runner timed out (`child-timeout`). The default 120s budget cannot fit
three agents of 180s each. Claude's frame stopped at the first-run prompt `5 new MCP servers
found in this project`, which `_dialog_key` does not answer and `_trust_dialog_stuck` does not
classify (spec `:63`, `:143`); its `Esc` needs input the spec says the ConPTY path lacks.
Unblock: accept that prompt once for this worktree, then run with a budget above 540s.

Codex's frame stopped at its own self-update (`npm install -g @openai/codex`, `EPERM` on the
running `codex.exe`). So launching it from the spec can change the host's global npm install.
