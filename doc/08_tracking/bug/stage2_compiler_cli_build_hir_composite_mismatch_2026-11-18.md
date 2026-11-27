# Stage-2 compiler_cli_build HIR failure: imported composite mismatched qualified declaration (pinned 917cf33)

Date: 2026-11-18
Host: Windows 11, x86_64-pc-windows-msvc
Lane: criterion-2 full bootstrap, pinned source 917cf33bdd6e, stage-2
compiler admitted and qualified, stage2-compiler-tests campaign
(bootstrap-20261118T084453Z-257)

## Observation

`compiler_cli_build` (slim profile matrix task) FAILS while every other
measured build passes:

```
error: in-process native-build: HIR lowering error in src/app/editor/tui_shell.spl:
       imported composite `EditorLocation` has a mismatched qualified declaration
error: ... imported composite `EditCommand` has a mismatched qualified declaration
error: ... imported composite `EditResult` has a mismatched qualified declaration
error: in-process native-build: HIR lowering error in src/app/editor/editor_ctrl_core.spl:
       imported composite `EditCommand` / `EditResult` / `EditorPropertyPayload` ...
```

Consequences: the slim profile verification reports missing required PASS rows
for compiler_cli_build, compiler_bootstrap_tests, interpreter_interpreter_tests,
loader_interpreter_tests (downstream of the cli build), and the generation is
rejected (`stage-engine-failed`; see
`c41full/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log`).

The same shape was previously mis-diagnosed as a `--jobs=half` scheduling
artifact (PR #10158); with `--jobs=1` and a retry-tolerant RSS watchdog
(PR #10245) the campaign completes 3h12m / 8h budget and the failure is shown
to be this genuine HIR lowering error.

## Analysis

- The stage-2 compiler that fails was itself built (1579 modules, 0 failed)
  from the same pinned sources, including the editor modules — so the editor
  sources are internally consistent at stage-2 build time. The failure
  appears only when the stage-2 compiler builds the *CLI entry closure*
  (`compiler_cli_build`), i.e. a cross-module composite re-export/import
  identity case the stage-2 native-build route did not exercise the same way.
- "Mismatched qualified declaration" = the composite's qualified name at the
  import site differs from its declaration site (re-export path alias).
- Upstream between 917cf33..d2550050b2f contains HIR-touching fixes
  (ca2b3c3065a Stage-4 HIR/MIR lowering; 0448bdb42c1; d5fea371da0) and two
  editor file changes (editor_controller.spl, gui_shell_render.spl), but NOT
  the failing files (tui_shell.spl, editor_ctrl_core.spl).

## Hypotheses (ranked)

1. The pinned compiler's HIR composite-identity check has a false-positive on
   editor re-exports, fixed upstream. Re-pinning at current release/1.0.0
   resolves it (stage-2 is seed-built from pin sources).
2. Genuine source inconsistency that newer compilers tolerate; then the fix
   is aligning the import/declaration qualified names of EditorLocation /
   EditCommand / EditResult / EditorPropertyPayload in
   src/app/editor/tui_shell.spl + editor_ctrl_core.spl with their declaring
   modules.

## Next step

Criterion-2 attempt #6 (final of the 6-cycle cap): re-pin at current
release/1.0.0 head, re-mint the stage4 planner-admission receipt, relaunch
with the same known-good command shape (jobs=1, patched watchdog). If the
same HIR errors recur, pursue hypothesis 2 by diffing the composite
declaration sites against the failing imports.

## Update 2026-11-19 — attempt #6 re-pinned at 41ea2084e43

Criterion-2 attempt #6 re-pinned the campaign source at release/1.0.0 head
`41ea2084e43` (98 commits past the d2550050b2f rebase base; prior campaign pin
was 917cf33bdd6e). Additional upstream HIR fixes now in the pin:
`b981dfbf38b` (release resolution sort scratch), `d0086d14b92` (reclaim
replaced import/export routes), `16006bb319e` (reclaim superseded surface
arrays at freeze), plus `5f1c299e96f` (bootstrap AOT opt_level decoupling).
Stage-2 build launched 2026-11-19 in pinned tree under
`.build/mcp-release-v7-source` (campaign dir c42s2). If the stage-2
compiler-tests campaign now records compiler_cli_build PASS, hypothesis 1
(driver predated upstream HIR fixes) is confirmed; if the same editor
composite mismatch recurs identically, hypothesis 2 (genuine source
inconsistency in tui_shell/editor_ctrl_core import qualified names) applies
and the composite declaration sites must be aligned with the import sites.
