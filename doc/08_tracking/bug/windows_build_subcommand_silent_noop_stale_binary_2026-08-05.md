# `bin/simple build` (incl. `build bootstrap`) silently no-ops on native Windows

Date: 2026-08-05
Status: OPEN
Area: bootstrap / deploy / CLI surface (Windows)

## Symptom

On native Windows (`bin/simple` -> `bin/release/x86_64-pc-windows-msvc/simple.exe`,
file-dated 2026-04-23), every form of the documented build command exits 0 with
**zero bytes** of stdout/stderr, foreground or backgrounded, redirected to a real
file (not a `head`/pipe artifact):

```
bin/simple build                    # exit 0, no output
bin/simple build bootstrap          # exit 0, no output
bin/simple build bootstrap --verbose  # exit 0, no output
bin/simple build --help             # exit 0, no output
```

`bin/simple --help`, `bin/simple --version`, and `bin/simple test <spec>` all work
normally on the same binary — the break is isolated to the `build` subcommand.

## Root cause (partially diagnosed)

`src/app/cli/_CliMain/main_and_help.spl` dispatches `"build"` to `handle_build`
via a **static** import (`use app.build.cli_entry.{handle_build}`), not through
the generic `app_path` table in `src/app/cli/dispatch/table.spl` — so that
table's (also-stale) `build` entry is dead code for this path and not the cause.

Initial hypothesis (stale `app_path: "src/app/build/main.spl"` — the file was
renamed to `cli_entry.spl` in `7f5a55fa46`, restoring an older `table.spl` during
a truncated-tree recovery) was checked and ruled out for this reason. Fixed the
stale path anyway (harmless cleanup, matches the `run`/`clean` sibling
convention) but it does **not** explain the symptom.

Most likely explanation, by analogy with
`doc/08_tracking/bug/bin_simple_bootstrap_main_stage_deployed_no_subcommands_2026-08-01.md`
(same failure class on Linux, same week): the deployed
`bin/release/x86_64-pc-windows-msvc/simple.exe` is simply **stale** (April vs.
current HEAD, which has seen multiple truncated-tree incidents and reverts since)
and its compiled-in `handle_build`/`cli_native_build` predates whatever current
source does. Not proved by binary inspection (no `strings`-equivalent identity
probe run on Windows yet) — flagging as most-likely, not confirmed.

## Why it can't be fixed by redeploying on Windows right now

`scripts/bootstrap/bootstrap-windows.sh --deploy` (the documented Windows
bootstrap path, delegating to `bootstrap-from-scratch.sh`) fails immediately:

```
error: Stage 4 full-CLI capsule preparation requires native Linux or macOS
```

This is intentional, not a regression — `bootstrap-from-scratch.sh` forces
`full_cli=1` whenever `--deploy` is passed (line 297), and refuses non-Linux/
Darwin hosts whenever `full_cli=1` (line 435-442). The `deploy` block itself
(line 2071+) consumes Stage 4's output (`${full_bin}`) directly, so there is no
narrower flag combination that reaches a deployable artifact on native Windows.
Per `.claude/rules/board-runnable.md`-style policy this should route through a
Linux-like proxy (WSL) rather than being silently skipped — filing this instead
of attempting that now, since building a cross-compile (e.g. mingw-w64 in WSL
targeting `x86_64-pc-windows-gnu`) is out of scope for the task that surfaced
this.

## Impact

`bin/simple build` / `bin/simple build bootstrap` are unusable on native Windows
until either (a) a fresh binary is cross-built/deployed via a Linux-like host and
copied into `bin/release/x86_64-pc-windows-msvc/`, or (b) Stage 4 gains a
native-Windows-capable path. `bin/simple test`, `lint`, `fmt`, `check`, `run`
are unaffected — verified working on the same (stale) binary.

## Follow-up 2026-08-05 — full test-suite run confirms downstream impact (PROVED)

Running `bin/simple test` (full `test/`) on the stale April self-hosted
binary: **19197 files, 292830 assertions passed, 135 assertions failed**
across ~68 spec-file hits (~40 unique specs once `test/unit/**` legacy-path
duplicates of `test/01_unit/**` are collapsed — both trees are real on-disk
duplicates of the same file content, not symlinks).

Sampling several failing specs individually showed a consistent signature:
**parse errors**, not assertion failures — e.g. `expected expression, found
Colon`, `expected pattern, found Case`, `expected Colon, found Comma`,
`expected expression, found Dot`, `expected expression, found Comma` — on
ordinary, unremarkable-looking `match`/`val`/type-annotation syntax.

Most of the compiler-area failing specs carry their own
`**Bug:** doc/08_tracking/bug/<name>_2026-0{7,8}-*.md` header, e.g.
`compound_assign_lowering_spec.spl` -> `jit_struct_field_compound_assign_loads_zero_2026-07-27.md`,
`enum_payload_subpattern_spec.spl` -> `enum_payload_subpattern_always_matches_2026-08-01.md`,
`naked_struct_pattern_match_arm_spec.spl` -> `naked_struct_pattern_vs_option_always_wildcard_2026-07-29.md`,
`parser_inline_match_in_argument_list_spec.spl` -> `parser_inline_match_terminated_by_list_2026-08-01.md`,
`parser_leading_operator_continuation_spec.spl` -> `parser_leading_operator_line_continuation_2026-08-01.md`,
`parser_true_false_prefix_call_arg_spec.spl` -> `parser_true_false_prefix_call_arg_2026-08-01.md`,
`return_terminates_spec.spl` -> `top_level_return_falls_through_2026-08-01.md`,
`array_at_option_spec.spl` -> `array_at_returns_nil_for_every_index_2026-08-01.md`.
Every one of these is dated 2026-07 or 2026-08 — **pre-existing and already
tracked**, several explicitly multi-lane (interpreter/JIT/native-LLVM/pure-Simple
native-build) with some lanes already fixed and others still open per their own
docs. These are regression-tracking specs written to pin down already-known
compiler bugs, not new defects this run discovered.

**PROVED, not inferred:** ran `array_at_option_spec.spl` through the June-1
Rust-seed binary (`src/compiler_rust/target/bootstrap/simple.exe`, itself
~2 months stale relative to HEAD, via `SIMPLE_BOOTSTRAP=1 ... test <spec>`).
It **parsed successfully** for 11 assertions, all failing logically. This
proves the April self-hosted binary's parse error on the same file is a
staleness artifact of that specific binary — a different (still not current,
but less old) binary parses the identical source without error. It does
**not** prove the underlying `.at()` logic bug is fixed (the referenced doc
says the pure-Simple `native-build` lane is still OPEN), only that the parse
layer has moved on since April.

Conclusion: essentially all 135 failures are explained by (a) pre-existing,
already-tracked compiler/runtime bugs under active multi-lane work, not new
regressions, and (b) a stale Windows binary whose parser predates several
2026-07/08 fixes. No src/test edits were made against these — fixing them
here would duplicate or conflict with the tracked lanes. Per goal instruction,
recording rather than "correcting."

## Separate Windows-only defect found during the same run

`bin/simple test` printed, once, near the end of the full run:

```
Warning: Failed to update test database: Cannot create a file when that file already exists. (os error 183)
```

`os error 183` is `ERROR_ALREADY_EXISTS` — classic Windows-only failure mode
for code that does a create-new/rename-without-replace where POSIX `rename()`
would silently clobber. Did not block the run (logged as a warning, exit
status driven by the 135 real failures instead), but the test database update
itself silently did not happen. Not investigated further — flagging for
whoever owns the test-runner's DB-write path (likely
`doc/08_tracking/test/test_db.sdn` writer) to make the write atomic/
replace-safe cross-platform (e.g. write-temp + `MoveFileEx` with
`MOVEFILE_REPLACE_EXISTING`, or the Rust `tempfile` + `persist` pattern).

## Critical separate Windows-only defect found during the same run: massive worker-process leak

`bin/simple test` (full `test/`, 19197 files) leaked **28,396** `simple.exe`
child processes on Windows — confirmed via `Get-Process -Name simple`, all
started within the run's timestamp window (10:25-10:41 AM), each with ~0.2-0.4s
total CPU time (idle, not hung — `Responding: True`), each holding ~12-13 MB
working set. Aggregate effect: system free memory dropped from a normal
baseline to **~2.5 GB free out of 66.8 GB total RAM**, and the process/handle
pressure caused unrelated tools to start failing with genuine OS-level resource
errors for the rest of the session:

- `jj status`: `Internal error: Unexpected error from backend / The paging file
  is too small for this operation to complete. (os error 1455)`
- `jj status` (later): `Could not read data at '.git\objects\...' / Insufficient
  system resources exist to complete the requested service. (os error 1450)`
- `git status`: separately hit a missing-`git-lfs`-binary error, but general git
  plumbing (`cat-file`, `read-tree`, `commit-tree`) kept working throughout,
  suggesting jj's higher-level working-copy scan is more sensitive to this
  resource exhaustion than raw git plumbing calls.

Recovery: `Get-Process -Name simple | Stop-Process -Force`, run repeatedly
(the process count was still climbing/draining slowly under the same resource
pressure — took several minutes across multiple batches to reach 0). After the
sweep: 0 leftover `simple` processes, free memory back to 53.7 GB.

This is almost certainly a **process-reaping/lifecycle bug specific to the
Windows test-runner path** — each spec file (or some subset, e.g. those using
process-isolation/sandbox execution) appears to spawn a child `simple.exe`
worker that is not waited-on/killed after the parent collects its result. Not
diagnosed further (no time taken to trace the spawn site), but severity is
high: a single `bin/simple test` full-suite run on Windows can, unattended,
degrade the host machine to the point of other tools failing with OS resource
errors, with no warning printed by the test runner itself.

## Suggested follow-up

1. Confirm staleness directly: run the identity/behavioural probes from
   `bin_simple_bootstrap_main_stage_deployed_no_subcommands_2026-08-01.md`
   against `bin/release/x86_64-pc-windows-msvc/simple.exe`.
2. Decide the intended Windows deploy path: WSL/mingw cross-compile producing a
   `x86_64-pc-windows-gnu` (or `-msvc`) artifact, vs. relaxing the Stage 4 host
   gate for a Windows-native capsule build.
3. Once a fresh Windows binary is deployable, add the same
   redeploy-gate/identity-marker check documented in the 2026-08-01 doc so this
   class of incident (stale-but-plausible binary silently serving an old command
   surface) is caught automatically instead of discovered by a silent no-op.
