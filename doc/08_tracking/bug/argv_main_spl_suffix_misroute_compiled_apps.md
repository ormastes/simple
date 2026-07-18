# Bug: `ends_with("main.spl")` argv-skip misroutes user files in compiled apps

Date: 2026-06-11
Status: fixed (2026-06-11, B7 sweep — all 22 latent sites replaced with precise per-app predicates matching only the app's own entry script path; see sweep notes below)
Severity: medium (silent wrong behavior — program never runs, exit 0)

## Symptom

A compiled Simple app whose `get_cli_args`-style helper skips `argv[1]`
when it `ends_with("main.spl")` silently swallows any USER file whose
name suffix-matches (`main.spl`, `h_main.spl`, `xmain.spl`,
`sub_test_main.spl`) and falls through to REPL/default dispatch with
exit 0. This was stage4's "9th site": byte-identical content under a
different filename ran fine.

## Root cause

The skip is a heuristic for interpreted mode (`bin/simple
src/app/X/main.spl args...`, argv[1] = the script itself). In a
compiled binary argv[1] is the user's file, so the suffix check is
wrong there.

## Fixed

- `src/app/cli/main_part1.spl` (2026-06-11): precise
  `arg_is_cli_entry_script()` predicate matching only
  `*/app/cli/main.spl`, `src/app/cli/main.spl`, `app/cli/main.spl`,
  and `bootstrap_main.spl` forms. Verified in docker: `*main.spl`-named
  user files now execute.

## Latent copies (same idiom, same misroute when compiled)

- `src/app/repl/main.spl:124`
- `src/app/tooling/main.spl:236`
- `src/app/check/main.spl`
- `src/app/context/main.spl`
- `src/app/test_runner_new/test_runner_config.spl:20`
- `src/app/jj/main.spl`
- `src/app/cli_debug/main.spl`
- `src/app/jupyter_kernel/main.spl`
- `src/app/linker_gen/main.spl`
- (plus remaining hits of `grep -rn 'ends_with("main.spl")' src/app`)

Inverse case: `src/compiler/10.frontend/core/interpreter/cli_eval.spl:153`
only skips the interpreted script path when it happens to be named
`*main.spl` — wrong for scripts with other names.

## B7 sweep (2026-06-11)

All latent copies fixed with precise per-app predicates:
- `src/compiler/10.frontend/core/interpreter/cli_eval.spl:153`
- `src/compiler/90.tools/duplicate_check/main.spl:27` (bare fallback removed)
- `src/app/repl/main.spl:124`
- `src/app/tooling/main.spl:236`
- `src/app/check/main.spl`
- `src/app/context/main.spl`
- `src/app/test_runner_new/test_runner_config.spl:20`
- `src/app/jj/main.spl`
- `src/app/linker_gen/main.spl`
- `src/app/cli_debug/main.spl`
- `src/app/itf/main.spl`
- `src/app/js/main.spl`
- `src/app/jupyter_kernel/main.spl`
- `src/app/pkg/main.spl`
- `src/app/serial_mcp/main.spl`
- `src/app/sim/main.spl`
- `src/app/simple_lsp_mcp/main.spl`
- `src/app/snpm/main.spl`
- `src/app/task_daemon/main.spl`
- `src/app/qemu/main.spl`
- `src/app/simple_portal/main.spl`
- `src/app/simple_process_manager/main.spl`
- `src/app/sj/main.spl`
- `src/app/sj_daemon/main.spl`
- `src/app/spipe_process_harness/main.spl`
- `src/app/office/mod.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_config.spl`

Flat_ast_bridge and driver_source_loading use `bootstrap_main.spl` suffix checks which remain correct (they match only bootstrap_main.spl specifically, not bare main.spl).

## Principled fix (proposed)

Add an `rt_is_compiled()` extern (native impl in
`src/runtime/runtime.c`; the interpreter returns false) and branch the
argv-skip on it instead of filename heuristics. Requires the
extern-addition bootstrap rebuild
(`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — see
feedback_extern_bootstrap_rebuild). Until then, port the
`arg_is_cli_entry_script` predicate to each listed entry point.
