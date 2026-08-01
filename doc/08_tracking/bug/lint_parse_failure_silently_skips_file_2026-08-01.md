# A file `lint` cannot parse is reported as one error, not as NOT LINTED — the file is silently skipped

**Date:** 2026-08-01
**Status:** Reporting FIXED (loud + countable + fail-closed). The census of how
many files are currently skipped is PARTIAL — see "Blast radius".
**Severity:** HIGH — this is a verification-layer blindness, not a cosmetic one.
A skipped file reads as a checked file.
**Area:** `simple lint`
**Binary used for every measurement below:**
`bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(the live `bin/simple` still has no `lint` subcommand — see
`reference_live_bin_simple_lost_all_subcommands_2026-08-01`).

## Defect

`compiler.tools.lint.main.lint_cli_source` gates every AST-based lint behind a
parse:

    val parse_failed = parse_module_silent_checked(content, path)
    if parse_failed:
        results.push(PARSE001 ...)
        return results          # <-- everything below is skipped

So when a file does not parse, `ARG*`, `COLL*`, `STUB*`, `W0406` (parsed export
sibling), wide-public and the riscv-rtl lint never run on it. Only the
text-pattern lints from `linter.lint_source` survive.

The damage is in how that was **reported**. Before this change the run said:

    test/fixtures/lint/dirty.spl:1:0: error[PARSE001]: Source did not parse

    Found 1 error(s), 0 warning(s), 0 auto-fix(es) available

    Lint failed in 1 file(s)

A file that was analysed **less** than a clean file reads as "checked, one
problem". There is no count of skipped files anywhere, so a repo-wide run
cannot tell you how much of the repo it actually looked at. This is the third
member of the same family, after
`lint_does_not_detect_syntax_errors_2026-07-28.md` (lint had no parse gate at
all) and `repo_verification_layer_is_fail_open_2026-07-28.md` (~70 of 92 check
scripts fail open).

## Fix

Reporting only — the gate itself is correct and is deliberately left in place.

1. `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
   - the PARSE001 message now reads
     `NOT LINTED: source did not parse - every AST-based lint was skipped for this file`
   - `run_lint_file` returns a distinct code **3** = NOT LINTED, so callers can
     count skipped files apart from analysed-and-faulty files. 3 is nonzero on
     every caller, and it is returned even if a future config downgrades
     PARSE001 below `Deny` (then `error_count` would be 0 while the file was
     still never analysed) — fail-closed by construction.
   - a loud per-file banner `NOT LINTED: <path> - source did not parse, so no
     AST-based lint ran on it`, plus a `{"type":"lint-not-linted"}` JSON line
     and a `not_linted` flag on the per-file JSON summary.
   - the standalone `simple_lint` entry normalises 3 to 1 so its exit contract
     is unchanged.
2. `src/app/io/cli_lint_commands.spl` and
   `src/app/io/_CliCommands/run_commands.spl` (both `lint` CLI paths)
   - count `not_linted_files`, print
     `NOT LINTED: N file(s) could not be parsed and were never analysed`
     above the failure summary, add `not_linted_files` to the JSON summary, and
     force a nonzero exit whenever the count is > 0 — so no summary path can
     report `Lint passed: all files clean` while any file was skipped.

Regression coverage: four new cases in
`test/03_system/app/lint_cli_contract_spec.spl` (loud + countable text output,
never-passed-with-a-skip across a mixed pair, JSON count, zero-count on a clean
run).

### RED / GREEN (measured, same binary, same tree)

RED, before the change (`lane_probe/ec_garbage.log`, an unparseable fixture):

    ...:1:0: error[PARSE001]: Source did not parse
    Found 1 error(s), 0 warning(s), 0 auto-fix(es) available
    Lint failed in 1 file(s)

No occurrence of "NOT LINTED" anywhere in the run.

GREEN, after (exit 1), with a live clean control in the same session that still
exits 0 and prints `Lint passed: all files clean`:

    ...:1:0: error[PARSE001]: NOT LINTED: source did not parse - every AST-based lint was skipped for this file
    NOT LINTED: <path> - source did not parse, so no AST-based lint ran on it
    Found 1 error(s), 0 warning(s), 0 auto-fix(es) available
    NOT LINTED: 1 file(s) could not be parsed and were never analysed
    Lint failed in 1 file(s)

JSON mode, same input:

    {"type":"lint-not-linted","file":"...","reason":"parse failure"}
    {"type":"lint-file-summary","file":"...","errors":2,"warnings":1,"fixes":0,"not_linted":true}
    {"type":"lint-summary","status":"failed","failed_files":1,"not_linted_files":1}

## Blast radius — PARTIAL, do not quote as final

Measured with `lane_probe/parse_gate_census.spl`, a probe that calls the exact
gate `lint` uses (`parse_module_silent_checked` + parser-state restore) over a
file list, so one process startup covers many files. Non-vacuity proved first on
a 3-file list: the unparseable fixture was flagged, a leading-operator
continuation file and a real source file were not.

**At least 143 `.spl` files fail lint's parse gate**, found within the first
~2,418 of 32,023 `.spl` files under `src/`, `test/` and `scripts/` (the run was
still in progress; the list is sorted, so the covered prefix is
`src/a*` .. `src/web_stack_sample`). That is a ~5.9% skip rate on the covered
prefix. Extrapolation is NOT warranted — `src/app/llm_caret/claude_full/` alone
contributes a large cluster — but the covered prefix is already enough to show
the number is in the hundreds, not single digits.

**TODO(lint,P1): finish the full 32,023-file census and record the exact count
and the per-directory breakdown here.** The probe and the file list are the
whole harness; it needs roughly 8 h of wall clock on a loaded host.

Note the CLI cannot be used for this census directly: `simple lint <dir>` dedupes
targets with a linear `seen_files.contains()` scan, which is O(n^2) and does not
terminate in practical time at 32k files. That is a separate defect.

**TODO(lint,P2): replace the O(n^2) target dedupe in
`app.io.cli_lint_commands.run_lint_command` with a set/dict-backed membership
test so a repo-scale directory target is usable.**

## What was NOT the defect

The brief for this lane described a *grammar* divergence: a leading-`+`
continuation line inside a function body accepted by the compiler and rejected
by lint. **That is already fixed at tip.** `lint` does not have a second
parser — `entry_and_fixes.spl` imports `compiler.core.parser`, the same
self-hosted frontend, and the leading-operator rule `69d3e4db82b` added to
`src/compiler/10.frontend/core/lexer_struct.spl` is therefore live in `lint`.
Verified directly at tip `a890bd17e1aa`: a leading `+` binding, a leading `==`
binding and a leading `>` inside an `if` condition all lint clean, while a
genuinely broken file still trips PARSE001 in the same session. The one
remaining parser divergence is the Rust bootstrap seed rejecting *leading*
comparison/equality operators, already recorded in
`parser_leading_operator_line_continuation_2026-08-01.md`.

The lesson stands regardless, and is why the reporting fix matters more than the
grammar fix did: the next grammar divergence will again mask a whole file, and
until now nothing would have counted it.
