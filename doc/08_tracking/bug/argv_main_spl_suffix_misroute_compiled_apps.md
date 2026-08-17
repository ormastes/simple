# Bug: `ends_with("main.spl")` argv-skip misroutes user files in compiled apps

Date: 2026-06-11
Status: fixed (2026-08-17) — see "Correction 2026-08-17" below. The earlier
`fixed (2026-06-11, B7 sweep)` stamp was FALSE: the sweep was incomplete and its
cited fix file never existed.
Severity: medium (silent wrong behavior — program never runs, exit 0)

## Correction 2026-08-17 — this record was falsely marked resolved

The 2026-06-11 closure claimed "all 22 latent sites replaced with precise
per-app predicates". Two things were wrong with it:

1. **The cited fix file never existed.** The "Fixed" section below points at
   `src/app/cli/main_part1.spl`. There is no such file in the tree, and git
   history has none. The precise predicate that section describes does exist,
   but at `src/app/cli/_CliMain/args_and_os_commands.spl:38`
   (`arg_is_cli_entry_script`), used at :71.
2. **At least one live site was never converted.** `src/app/cli_util.spl:32`
   still carried the bare heuristic
   `if all_args.len() > 1 and all_args[1].ends_with("main.spl"):` inside
   `get_cli_args()`, with the buggy behaviour documented as intended in the
   docstring at :18. That file neither imported nor called
   `arg_is_cli_entry_script`.

### Real fix (2026-08-17)

`src/app/cli_util.spl` now exports a path-parameterised predicate instead of a
filename-suffix test:

- `arg_is_entry_script(arg: text, entry_rel: text) -> bool` — matches the bare
  entry path, the `src/`-prefixed form, or a trailing path-component match; it
  cannot match an unrelated user argument such as `build/h_main.spl`.
- `strip_entry_script(raw: [text], entry_rel: text) -> [text]` — pure over the
  raw argv, so routing is testable without a process.
- `get_cli_args(entry_rel: text)` — each caller now names its own entry script.

Why a generalisation rather than importing `arg_is_cli_entry_script`: that
predicate is hard-coded to the CLI's own three entry paths, so it is not
correct for `check_dbs`/`ffi_gen`, and its module deliberately bypasses the
`app.io.mod` hub for CLI startup latency — importing `app.cli_util` there would
pull the hub onto the hot path. No new module was created and the logic is not
duplicated: cli_util owns the general form, the CLI keeps its specialisation.

Consumers updated: `src/app/check_dbs/main.spl:227` passes
`"app/check_dbs/main.spl"`; `src/app/ffi_gen/test_all_mods.spl` imported
`get_cli_args` but never called it, so the unused import was removed.

Census 2026-08-17: `grep -rl 'ends_with("main.spl")' src/app src/lib` now
returns exactly one file — `src/app/cli/_CliMain/args_and_os_commands.spl` — and
only inside a comment describing the anti-pattern. No executable site remains.

Regression specs:
- `test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl` (reproducer)
- `test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl` (defect class:
  scans owned app source for a suffix test used as a routing condition, with a
  positive control so a clean sweep cannot mean a broken scan)

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

## Fixed (2026-06-11 claim — file path is WRONG, see Correction above)

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
