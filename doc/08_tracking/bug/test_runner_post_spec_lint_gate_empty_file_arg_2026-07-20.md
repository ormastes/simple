# test-runner post-spec lint gate invokes simple_lint with an empty/missing file arg

**Status:** open
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
