# A file `lint` cannot parse is reported as one error, not as NOT LINTED — the file is silently skipped

**Date:** 2026-08-01
**Status:** Reporting FIXED (loud + countable + fail-closed). The census of how
many files are currently skipped is RETRACTED — the oracle was proved vacuous by
sabotage; see "Blast radius". Do not cite any count from this lane.
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

## Blast radius — RETRACTED, no number is publishable yet

An earlier revision of this doc published "at least 143 files" and an earlier
lane report circulated ">= 304". **Both are withdrawn.** The oracle that
produced them is broken in a way that makes every per-file verdict untrustworthy.
Do not cite any count from this lane.

### Why the oracle is void — PROVED by sabotage

The probe (`lane_probe/parse_gate_census.spl`) called
`compiler.core.parser.parse_module_silent_checked`, the same entry `lint` uses,
once per file in one process. To validate it, the tree copy of that function in
`src/compiler/10.frontend/core/parser.spl` was sabotaged to

    fn parse_module_silent_checked(source: text, path: text) -> bool:
        print "SABOTAGE_MARKER_TREE_PARSER_IS_LIVE"
        return true
        ...original body, now unreachable...

On a two-file list (one file that parses, one that does not) the marker printed
**twice** — so the tree function really was entered for both files — yet the
probe still reported exactly **one** file as unparseable, identical to the
unsabotaged run. An unconditional `return true` did not change a single verdict.

The value the call site consumes is therefore **not** the return value of the
implementation it names. Something else — a host-side parse in the seed binary —
is supplying the verdict. A gutted implementation and an intact one are
indistinguishable to this probe, which is the definition of a vacuous oracle.
A narrower earlier sabotage (`CoreLexer.leading_op_continues` forced to
`return false`) likewise changed nothing, which was the first warning sign.

### Second, independent invalidation

Even with a sound oracle, the measurement shape was wrong.
`parse_module_silent_checked` does not reset parser/AST state between calls
(a sibling lane proved this, and retracted four "crisp" cap boundaries that
turned out to be artifacts of exactly this). Every shard here was **one process
scanning ~4,000 files**, so per-file verdicts were order-dependent, not a
property of the repo. The corroborating symptom was visible in this lane too:
the single-process run reached **8.9 GB RSS after 4,363 files** and kept
climbing — state accumulating, never released. That, not the O(n^2) target
dedupe and not host contention, is the best explanation for the shard that died
without emitting a summary. (The re-run of that shard was checked directly: state
`S`, 9.8 s CPU per 10 s wall, output file still advancing — CPU-bound and
progressing, not wedged.)

### What a trustworthy census would require

1. **One process per file**, or per small chunk, so no cross-file state leaks.
   The pattern a sibling lane validated: 11,310 files, 40 chunks x 379, one
   process per chunk, pristine vs patched, compared as **sets** not counts
   (417 = 417 identical FAIL sets, 0 incomplete chunks).
2. **An oracle that fails when sabotaged.** Any replacement probe must first be
   shown to flip its verdict when the implementation under test is gutted.
   This one did not.
3. **The instrument named next to the number**, always: binary path and build
   date. Everything in this lane used
   `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`,
   **built Jul 30**, which predates `6587c9e8875` (assignment-RHS continuation)
   and `a7e5fbccf85` (elif trailing operator). Both are ancestors of the tree
   that was scanned, but since the verdict came from the host binary rather than
   the tree, the binary's date is load-bearing and both fixes are missing from
   it.
4. **Scope decided before counting.** Two of the largest apparent clusters are
   probably not live lint risk at all and must be split out rather than folded
   into a headline: `src/compiler_rust/lib` is the Rust seed's bundled stdlib
   and may be entirely out of scope for the pure-Simple lint gate, and
   `src/app/interpreter` is separately known to be unexercisable by specs (zero
   external importers), so its share may be dead code.

**TODO(lint,P1): build a per-file-isolated, sabotage-validated census and only
then record a number here.**

Separately, and independent of the oracle problem: the lint CLI cannot perform
this census itself, because `app.io.cli_lint_commands.run_lint_command` dedupes
targets with a linear `seen_files.contains()` scan. That is O(n^2) and does not
terminate in practical time at repo scale.

**TODO(lint,P2): replace the O(n^2) target dedupe with a set/dict-backed
membership test so a repo-scale directory target is usable.** (Another lane is
reported to be fixing this.)

### What this does NOT invalidate

The NOT-LINTED reporting fix above. That was measured end-to-end through the
shipped `simple lint` CLI — real command, real stdout, real exit codes, RED
captured before the change and GREEN after with a live clean control in the same
session. It does not depend on the census oracle in any way.

## What was NOT the defect

The brief for this lane described a *grammar* divergence: a leading-`+`
continuation line inside a function body accepted by the compiler and rejected
by lint. **`lint` does not reproduce that rejection at tip** — measured
end-to-end through the shipped CLI at `a890bd17e1aa` with
`simple.pre-segv-fix-20260731` (built **Jul 30**): a leading `+` binding, a
leading `==` binding and a leading `>` inside an `if` header all lint clean,
while a genuinely broken file still trips PARSE001 in the same session. That is
a black-box observation of the shipped tool and it stands on its own.

**The explanation for it is NOT established, and an earlier revision of this doc
overclaimed it.** That revision said lint has no second parser, because
`entry_and_fixes.spl` imports `compiler.core.parser` and there is exactly one
`fn parse_module_silent_checked` in the tree
(`src/compiler/10.frontend/core/parser.spl:863`). Import graph and definition
count are *static* evidence; they do not establish what executes. The sabotage
recorded under "Blast radius" shows the opposite at runtime: gutting that
function to an unconditional `return true` changed no verdict, so under this
binary the parse verdict is served by the host, not by the tree copy. Which
parser implementation actually backs lint's PARSE001 gate is therefore **UNKNOWN
and must be re-established** before anyone relies on "the compiler's grammar fix
automatically reaches lint".

**TODO(lint,P1): determine, by sabotage rather than by import graph, which parser
implementation serves lint's PARSE001 gate under the deployed binary.** Until
that is answered, treat compiler-side grammar fixes as NOT automatically
reaching lint.

Note the related open item recorded in
`parser_leading_operator_line_continuation_2026-08-01.md`: the Rust bootstrap
seed was reported there to reject *leading* comparison/equality operators. This
lane observed the opposite through `lint` on the same binary, which is further
reason to distrust the static explanation and settle it by sabotage.

The reporting fix is what matters regardless, and is why it was landed first and
separately: the next grammar divergence will again mask a whole file, and until
now nothing counted it.
