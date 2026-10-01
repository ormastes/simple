# Phase 2 cli_debug noncanonical text and stdio symbols (2026-08-15)

Status: source fix applied; frozen rebuild and cache-preserving verification pending.

## Failure

The admitted Phase-2 compiler built 373 `cli_debug` objects with the `host-gpu`
runtime bundle, then the link failed. The exact first unresolved symbol was
`str.is_alphanumeric`, emitted from
`src/app/cli_debug/evidence_replay_v1.spl`. Later unresolved symbols were the
legacy aliases `stdout_flush` and `input` from `src/app/cli_debug/main.spl`.

Retained evidence:

- `build/debug_tools_phase2/logs/cli_debug.build.log`
- `build/debug_tools_phase2/logs/cli_debug.build.status`
- `build/debug_tools_phase2/logs/cli_debug.build.time`

The run exited 1 after 433.12 seconds with max RSS 815,576 KiB. Its 373-object
isolated cache is retained for one bounded retry.

## Bounded fix

- Replace the unsupported dotted text predicate with the existing explicit
  ASCII letter/digit range predicate while preserving `/._-` acceptance.
- Replace `stdout_write`, `stdout_flush`, and `input` in the entry module with
  the canonical core ABI symbols `rt_stdout_write`, `rt_stdout_flush`, and
  `rt_stdin_read_line_text`.
- Keep `host-gpu` and the exact admitted Stage-2 runtime authority. Do not add
  `libsimple_native_all.a` through an override.

## Verification gate

After frozen-manifest refresh, retry the exact retained `cli_debug` command
once with `cache_cli_debug` and the admitted Stage-2 compiler. The separate
CoreLexer blocker requires a Stage-2 rebuild, but this app-only fix does not.
Require a candidate, then run its help, JSON, invalid-command, and piped `quit`
smokes once. The existing semantic replay integration must continue to accept
`normalized/replay.sst` and reject shell-shaped unsafe paths.
