# test-runner post-spec lint gate invokes simple_lint with an empty/missing file arg

**Status:** FIXED (2026-08-06) — see "Resolution" below
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** app/test_runner (SSpec `simple test` harness)

## Symptom

`bin/simple test test/01_unit/tools/cat_spec.spl --no-session-daemon` reports
the spec as **FAILED** even though all `it`/`describe` examples inside the
spec pass cleanly:

```
  file reading
    ✓ reads existing file content
  line numbering
    ✓ counts lines correctly
  blank line squeezing
    ✓ detects blank lines
    ✓ detects non-blank lines

4 examples, 0 failures
Usage: simple_lint <file.spl> [options]

Options:
  --deny-all        Treat all warnings as errors
  --warn-all        Enable all style lints
  --profile=<tier>  Strictness tier: moderate | lib | reliable
  --json            Output in JSON format
  --fix             Apply safe auto-fixes
  --fix-all         Apply all fixes regardless of confidence
  --fix-dry-run     Show what would be fixed without applying
  --fix-interactive Prompt for each fix
...
error: test-runner: spec failed

=========================================
Test Summary
=========================================
Files: 1
Passed: 4
Failed: 1
Duration: 17367ms

FAIL test/01_unit/tools/cat_spec.spl
```

Note the `4 examples, 0 failures` line — the actual SSpec assertions all pass.
Immediately after, the runner shells out to `simple_lint` with **no file
argument**, which prints its own `Usage: ...` help text and exits non-zero.
The test-runner counts this as example #5 ("Failed: 1" beyond the 4 real
examples) and marks the whole spec FAIL.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/tools/cat_spec.spl --no-session-daemon
```

`test/01_unit/tools/cat_spec.spl` is the "TOOL-CAT" spec (`describe "cat
tool"`, 4 `it` blocks, all pure in-memory assertions, no subprocess calls).

## Root-cause hypothesis

`test/01_unit/tools/cat_spec.spl` exercises a "cat" CLI tool, but there is no
corresponding implementation file under `src/` (checked: no
`src/app/**/cat*.spl` matching a CLI-tool source). The post-spec gate in the
test runner appears to try to resolve/lint a "companion source file" for the
tool under test (likely a doc-coverage or per-tool lint check keyed off the
spec's path/feature id) and, when that companion source can't be resolved,
invokes `simple_lint` with an empty path instead of skipping the check. The
lint tool's own usage/help dump then gets misinterpreted as a lint failure
and folded into the spec's pass/fail tally.

**Update (second affected spec found, "missing companion source" theory
narrowed):** `test/01_unit/app/doc_coverage/compiler_integration_spec.spl`
hits the exact same symptom (`Usage: simple_lint ...` after all real
examples pass, `Passed: 8, Failed: 1`, overall FAIL) even though its
companion source (`src/app/doc_coverage/compiler_warnings.spl`,
`src/app/doc_coverage/scanner/mod.spl`) genuinely exists and was fixed this
same shard (see below) — ruling out "no companion source exists" as the
universal trigger. The gate more likely fires unconditionally after every
spec (or every spec under specific directories/categories) and invokes
`simple_lint` with a malformed/empty argument regardless of whether a
companion source resolves; only some specs happen to already have another
failure masking it, or the arg-building path itself is broken for some
other reason not yet isolated. Flagging as still the same class of harness
defect (empty/missing file arg passed to `simple_lint` post-spec, wrongly
counted as a spec failure), root trigger condition not fully pinned down.

This is a harness-level defect (outside the two affected spec files, both of
which are fully correct) — out of scope for a spec-only fix per this
campaign's rules (Rust seed / test-runner source fix needs a rebuild).

## Affected specs seen this shard

- `test/01_unit/tools/cat_spec.spl`
- `test/01_unit/app/doc_coverage/compiler_integration_spec.spl` — note: this
  spec ALSO had a genuine, separate, already-fixed source bug this shard:
  `src/app/doc_coverage/compiler_warnings.spl:43` accessed
  `item.has_inline_comment`, but `DocItem` (`src/app/doc_coverage/
  scanner/mod.spl:14-22`) declares the field as `has_comment`. Fixed
  (one-line field-name correction) and verified: all 8 real examples now
  pass (`8 examples, 0 failures`) — the spec is blocked ONLY by this
  harness-level lint-gate defect now, not by any remaining spec/src issue.

## Resolution (2026-08-06)

**The "post-spec lint gate" never existed as such.** Both the original
"missing companion source" hypothesis and the revised "unconditional
post-spec `simple_lint` invocation" hypothesis were wrong — there is no code
anywhere in `src/app/test_runner_new/`, `src/lib/nogc_sync_mut/test_runner/`,
or the CLI dispatch layer that shells out to (or in-process calls) the lint
tool after a spec's examples finish. Exhaustive grep across the repo for
`simple_lint`, `run_lint_file`, `lint_main(` and `companion` found no such
call site tied to spec execution.

### Root cause (confirmed)

Same underlying defect as
`doc/08_tracking/bug/test_runner_wildcard_imported_main_phantom_failure_2026-08-01.md`
("Site A" in that doc), just a different downstream symptom:

- The interpreter-mode test runner generates a synthetic entry point for
  every spec it executes: `src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`
  (`_preprocess_spipe_file`, ~line 479) always emits `fn main():` /
  `fn main() -> i64:` as the wrapper's actual entry point, wrapping the
  spec's real body.
- Before the fix, `src/compiler/90.tools/lint/main.spl` re-exported its
  `_LintMain.entry_and_fixes` submodule via a **wildcard**
  (`export use compiler.tools.lint._LintMain.entry_and_fixes.*`), and that
  submodule declared the lint CLI's entry point as a bare `fn main() -> Int`
  (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`, the function
  now named `lint_main` at line 289). Any spec whose dependency graph
  wildcard-imported `compiler.tools.lint.main` (directly or transitively)
  therefore had a second `fn main` land in scope alongside the runner's own
  synthesized one.
- On name collision the wrong `main` won and got invoked as the process
  entry point with no argument-passing plumbing (it is an in-process
  function call, not a subprocess with argv). `lint_main`'s own
  `args.len() < 2` guard (`entry_and_fixes.spl:293-317`) then fired and
  printed its `Usage: simple_lint <file.spl> [options]` banner, returning a
  failing status. The runner's aggregate parser folded that trailing
  non-zero return into the example tally as one extra failed "example",
  flipping an all-green spec to FAIL — exactly the `4 examples, 0 failures`
  followed by `Usage: simple_lint ...` / `Failed: 1` signature in this doc's
  symptom section. This explains why the trigger looked unconditional and
  path-independent: it depended on the spec's *import graph* reaching
  `compiler.tools.lint.main`, not on any lint-gate/companion-source logic at
  all (there was none).

### Fix (already landed, `.spl`-only)

Two coupled changes, both already present in current `main`:

1. `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:289` — the lint
   CLI's `fn main() -> Int` renamed to `fn lint_main() -> Int`.
2. `src/compiler/90.tools/lint/main.spl:24-29` — the facade's
   `export use ..._LintMain.entry_and_fixes.*` wildcard replaced with an
   explicit named list (`lint_cli_source, lint_cli_find_decl_line, ...,
   run_lint_file, collect_easy_fixes, apply_collected_fixes, lint_main`)
   that never binds a bare `main` symbol.

With no `fn main` reachable via wildcard from the lint module graph, nothing
can collide with the test-runner's synthesized entry point, so this specific
collision path is closed. (A companion, Rust-side mechanism — "Site B" in
the wildcard-main doc, binding an imported module's export dict under the
literal key `"main"` for `Group`/`Glob` targets regardless of which symbols
are named — is tracked separately in that doc and was still unverified as of
2026-08-01; it produces a different, distinct symptom, `error: semantic:
type mismatch: cannot convert dict to int`, not the `Usage: simple_lint`
banner this doc is about, so it does not reopen this bug.)

### Verification

Re-ran this doc's exact repro:

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/tools/cat_spec.spl --no-session-daemon
```

Before (doc symptom, 2026-07-20): `4 examples, 0 failures` immediately
followed by `Usage: simple_lint <file.spl> [options]` and `FAIL`.

After (2026-08-06, current `main`): clean run, no `Usage: simple_lint` text
anywhere in the output —

```
Passed: 4
Failed: 0
Results: 4 total, 4 passed, 0 failed
PASS test/01_unit/tools/cat_spec.spl
```

`test/01_unit/app/doc_coverage/compiler_integration_spec.spl` no longer
shows the lint-gate symptom either, but it now fails for a **separate, real,
unrelated** reason: `semantic: variable 'NL' not found` in 7 of 8 examples.
That is a genuine spec/source defect (not this harness defect) and is
explicitly left alone here — out of scope for this doc.

Broader spot-check (all specs run individually, sequential per
`.claude/rules/testing.md`, `grep -c "Usage: simple_lint"` == 0 in every
case):

- `test/01_unit/tools/*_spec.spl` (15 files) — **all PASS**, zero
  occurrences of `Usage: simple_lint`.
- `test/01_unit/app/doc_coverage/*_spec.spl` (14 files) — zero occurrences
  of `Usage: simple_lint`; 5 PASS, 9 FAIL for unrelated reasons (`Cannot
  resolve module: doc_coverage.*`, `variable 'NL' not found`, `array index
  out of bounds`) — a separate doc_coverage module-restructure regression,
  not this bug, not investigated further here.

No source change was required from this session: the fix was already
present in current `main` (landed as a side effect of the sibling
`test_runner_wildcard_imported_main_phantom_failure_2026-08-01` investigation,
which this doc was not previously cross-linked to). This doc was left open
only because it was never updated to point at that landed fix. Closing as
FIXED; the original investigation above is kept for context.
