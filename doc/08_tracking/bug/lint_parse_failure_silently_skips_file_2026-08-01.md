# A file `lint` cannot parse is reported as one error, not as NOT LINTED — the file is silently skipped

**Date:** 2026-08-01
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

Separately, and independent of the oracle problem: `run_lint_command` deduped
targets with a linear `seen_files.contains()` scan, which is O(n^2) at repo
scale.

**TODO(lint,P2): replace the O(n^2) target dedupe with a set/dict-backed
membership test so a repo-scale directory target is usable.** — **DONE**, see
below.

### O(n^2) target dedupe — FIXED, measured

`src/app/io/cli_lint_commands.spl` (`run_lint_command`) and the identical
sibling `src/app/check/targets.spl` (`expand_check_targets`, used by `simple
check`) both now dedupe with `{text: bool}` dict sets — `contains_key(k)` plus
`d[k] = true` — instead of `[text].contains()` + `.push()`. The `{text: bool}`
shape is deliberate: it never needs `Dict.len()` (returns -1 under native
codegen) and never `.get()`s a struct-valued dict, so it is safe on the
interpreter, the JIT and native codegen alike (`.claude/rules/code-style.md`).

Measured with a standalone microbenchmark that runs the two dedupe shapes over
N synthetic paths, one process per data point, binary
`bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`, `/usr/bin/time`
for wall and peak RSS. All runs verified `unique == N`.

| N | array `.contains()` wall | dict `contains_key` wall | array RSS | dict RSS |
|---|---|---|---|---|
| 1,000 | 0.28 s | 0.04 s | 62.5 MB | 63.2 MB |
| 2,000 | 0.63 s | 0.04 s | 63.5 MB | 63.7 MB |
| 4,000 | 2.60 s | 0.05 s | 64.5 MB | 64.8 MB |
| 8,000 | 11.49 s | 0.13 s | 66.0 MB | 66.8 MB |
| 16,000 | 55.03 s | 0.24 s | 70.1 MB | 70.3 MB |
| 32,023 | **239.80 s** | **0.27 s** | 78.3 MB | 79.1 MB |

The array form is textbook quadratic — 4.4x, 4.8x, 4.4x per doubling — and costs
**239.8 s of pure CPU at repo scale before a single file is linted**. The dict
form is flat at 0.27 s: an **888x** reduction, and it stays flat as N grows, so
this is a complexity fix and not merely a constant-factor one. Peak RSS is
unchanged (~78 MB either way), which also rules the dedupe out as the source of
the multi-GB single-process growth recorded above.

**Correction to the earlier claim in this file:** the array dedupe does *not*
literally fail to terminate — it terminates in ~240 s. It was never on its own
the reason a repo-scale lint run dies. Two other costs dominate and both remain
open: per-process lint startup measured at **273 s** for a 5-file directory and
**316 s** for a single 709-line file (same binary, same tree, loaded host), and
the unbounded cross-file RSS growth recorded above. Fixing the dedupe is
necessary but not sufficient for a CLI-driven census.

Functional check, same binary, tmpfs checkout of the tip tree: `simple lint
--json src/app/check` emits 5 `lint-file-summary` lines for 5 files, and
`simple lint --json src/app/check src/app/check ./src/app/check` — the same
directory three times, spelled two ways — still emits exactly 5. Dedupe
behaviour is preserved across both the target set and the discovered-file set.

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

## Census attempt 3 — oracle VALIDATED BY SABOTAGE, but the repo-wide count is still not measurable

**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(Jul 30). **Tree:** a tmpfs `git archive` of origin `931cf1dcf6555e34d69665149ac8ea14e6ec1488`.

### The binary's date does NOT make these verdicts stale — PROVED

The standing worry about this lane is that a Jul-30 host binary reproduces
already-fixed parser bugs. For *this* oracle that worry does not apply, and it
is provable rather than arguable: the host binary compiles `lint` **from the
source tree it is run in**. Two independent demonstrations, same binary:

1. The Jul-30 binary prints the `NOT LINTED:` banner that only landed in the
   tree on 2026-08-01. It cannot have had that string baked in.
2. Editing `src/compiler/10.frontend/core/parser.spl` in the tree changes the
   verdict (next section).

So the parser under test is the **tree's** parser at tip, not a Jul-30 snapshot.
The host binary's date is load-bearing for codegen, not for these parse
verdicts.

### Sabotage validation — the precondition the previous census failed

The previous census oracle was proved vacuous: gutting
`parse_module_silent_checked` did not change its verdict. The same sabotage was
therefore applied to this one before any file was counted.

`parse_module_silent_checked` in `src/compiler/10.frontend/core/parser.spl` was
replaced with an unconditional failure plus a marker:

    fn parse_module_silent_checked(source: text, path: text) -> bool:
        print("SABOTAGE_MARKER_PMSC {path}")
        true

Same command, same two fixtures, before and after
(`simple lint --json probe/good.spl probe/bad.spl`):

| | `probe/good.spl` | `probe/bad.spl` | `not_linted_files` |
|---|---|---|---|
| control | `errors:0`, no flag | `not_linted:true` | 1 |
| sabotaged | **`not_linted:true`** | `not_linted:true` | **2** |

The marker fired exactly twice, and the good file **flipped**. The verdict
demonstrably comes from the implementation named. This oracle is sound where
the previous one was vacuous. The parser was then restored and re-verified
byte-identical to the origin blob before any census file was run.

### Order-dependence

Measured, not assumed: linting `bad.spl` *before* `good.spl` still reports
`good.spl` clean, and `good.spl` alone is clean — so a preceding parse failure
did not contaminate the following file for this pair. That is one pair, not a
proof, so the census harness still uses **one process per file** and never
relies on batching.

### Harness

`census.sh` — one `simple lint --json <file>` process per file, verdict in
{LINTED, NOT_LINTED, TIMEOUT, CRASH}, nothing folded into "checked". It carries
its own positive and negative control in every run and asserts
`result count == input count`, exiting nonzero otherwise.

That assertion is not decorative. The first revision of the harness died on
`export -f` (fatal under dash), **linted zero files, and exited 0** — a silent
no-op that was caught only because the verdict tally was checked. This is the
same failure class as the retracted census and as
`reference_probe_harness_falls_through_exit_zero`.

### Measured throughput — why the repo-wide number is still out of reach

| workload | files | wall | effective |
|---|---|---|---|
| 2 tiny fixtures, 1 process | 2 | 7.3 s | — |
| 12 uniformly random repo `.spl`, 6-way | 12 | 121 s | ~10 s/file |
| cluster census, 8-way | — | — | **~30 s/file** |

At ~30 s/file effective, the full **31,998** `.spl` files under `src/`, `test/`
and `scripts/` is **~90 h of wall clock** on this host. That is the honest
blocker, and it is *not* the O(n^2) dedupe (fixed above, and worth only 240 s of
the total). It is per-file lint cost: a 3-line fixture costs ~3.5 s, while
`src/app/io/_CliCommands/run_commands.spl` (709 lines) costs **316 s** in a
single-file process — lint appears to pay for the linted file's transitive
module graph, so cost tracks imports, not line count.

**No repo-wide count is published here.** A uniform random sample of 12 files
returned 0 NOT_LINTED, which is consistent with a low single-digit percentage
but far too small to bound anything.

### What PARSE001 cannot tell you

The diagnostic is emitted at `<file>:1:0` with no line or construct, so this
oracle can enumerate *which* files fail but not *why*. A breakdown by failure
shape is therefore **not** cheaply available, and one plausible shape was tested
and refuted: `import a.b.{C}` at line 1 (used by 396 files) parses fine, so the
`import` keyword is not the cause in `src/app/interpreter/ast_types.spl`.

**TODO(lint,P2): give PARSE001 the parser's real line/column and message so a
census can group failures by cause instead of only listing paths.**

### Cluster census — IN PROGRESS, not a result

A one-process-per-file census of the two directories the retracted figures
named — `src/app/interpreter` (99 files) and `src/compiler_rust/lib` (725) — is
running at the time of writing and is **~7 h** at measured throughput. Do not
quote a number from it until it reports `CENSUS_OK` with
`result count == input count`. Partial prefixes are not results: the earlier
retracted census was a partial prefix.

Two scoping notes that must be settled before any count from it becomes a
headline, both confirmed here:

* `src/app/interpreter` has **zero external importers** (verified by grep for
  `app.interpreter.` across `src/` and `test/`, excluding the tree itself), so
  it is unexercisable by specs. Failures there are most likely **dead code, not
  live verification risk**, and must be reported separately rather than folded
  into a repo headline.
* `src/compiler_rust/lib/std` holds **682** of that directory's 725 `.spl`
  files — the Rust seed's bundled copy of the Simple stdlib. It is not in the
  declared external-paths list in `CLAUDE.md`, so it is nominally in scope, but
  it is a duplicate of `src/lib` shipped for the seed. Whether the pure-Simple
  lint gate is even meant to apply to it is an open scoping question, not a
  measurement question.

## Per-file lint cost — ROOT-CAUSED and FIXED (2026-08-01)

The `~90 h` blocker above is resolved. The stated hypothesis for it is
**REFUTED**, and the actual mechanism is unrelated to imports.

**Instruments.** Wall/RSS from `/usr/bin/time -v`, one process per data point.
Phase attribution from `rt_time_now_monotonic_ms()` timers inserted around every
call in `Linter.lint_source` and `lint_cli_source` (scratch tree only, never
committed). Binary `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`,
tree = a private checkout of origin `3807bab68e8` (109,576 entries), never the
shared working copy. Host was under load average ~16-20 from sibling lanes
throughout, so absolute walls are pessimistic; the *ratios* are the result.

### The transitive-module-graph hypothesis is REFUTED

The brief for this work said "lint appears to pay for the linted file's
transitive module graph, so cost tracks imports, not line count". It does not.

* `parse_use_decl` in `src/compiler/10.frontend/core/parser_decls_use.spl`
  performs **no file I/O at all** — no `file_read`, no module resolution. Lint's
  parse of a target file never loads that file's imports.
* Cost is **linear in the target's line count**, not in its import count:

  | target | lines | wall | marginal over the 3-line floor |
  |---|---|---|---|
  | 3-line fixture | 3 | 6.66 s | — |
  | `src/app/coverage/main.spl` | 248 | 99.86 s | 0.380 s/line |
  | `src/app/io/_CliCommands/run_commands.spl` | 709 | 297.26 s | 0.412 s/line |

  Two files whose import counts differ by 22 give the same per-line rate. The
  709-line file was "import-heavy" only incidentally; it was simply the biggest.

### The actual mechanism: `simple lint` never ran the JIT

Phase timers on `src/app/coverage/main.spl` (248 lines, 88.33 s wall in that run):

| phase | ms |
|---|---|
| `parse_module_silent_checked` (the target's own parse) | **74,564** |
| `check_stub_impl` | 5,170 |
| `check_collection_patterns` | 2,184 |
| **all 20 text lints together** (`lint_source`) | **1,471** |
| `check_all_rules` (of that 1,471) | 1,089 |
| everything else | < 100 each |

84% of the run is one call. The control: the same file goes through the native
compiler in **0.18 s** (`/usr/bin/time`, `simple compile`). A ~500x gap.

The cause is in the driver, not in lint.
`should_prefer_interpreter_for_source` in
`src/compiler_rust/driver/src/exec_core.rs` routes an app to the **interpreter**
whenever its entry source contains the substring `std.cli`, `get_cli_args` or
`rt_cli_get_args`. `src/app/cli/lint_entry.spl` line 6 is
`use std.cli.cli_util (get_cli_args)`, so **every `simple lint`, `simple fmt`
and `simple fix` invocation has always run fully interpreted.** That is cheap
for a short-lived CLI, but the linter runs the *pure-Simple parser* over every
target file, so the guard interpreted a whole parse per file — the ~100-1000x
class described on `jit_strict_fallback_error`, except silent: this is a
deliberate pre-JIT routing decision, so no `[jit-fallback]` marker is ever
printed. `grep` for that marker in a lint run returns **0 hits**.

### The fix, and why it is NOT yet the default — READ THIS BEFORE FLIPPING IT

The fix is to stop routing `lint_entry.spl` to the interpreter: a narrow
`is_jit_safe_cli_args_entrypoint()` allow-list in
`should_prefer_interpreter_for_source`, consulted before the CLI-args guard, an
**exemption rather than a removal** so every other CLI-args app keeps the
interpreter route byte-for-byte. That patch was written, compiles, and its three
new unit tests pass alongside the ten pre-existing `exec_core` tests
(`cargo test -p simple-driver --lib exec_core`: 13 passed, 0 failed) — including
one asserting an unrelated CLI-args app is *still* sent to the interpreter.

**It is deliberately not committed, because flipping the route changes lint
output.** See the A/B below: the JIT emits false-positive MODINIT001 warnings
that the interpreter does not. Shipping it would push a lint false positive
across the whole repo, which is exactly the kind of trade this bug file exists
to refuse.

What is available **today**, with no rebuild, for anyone who needs the throughput
and can tolerate the known divergence:

    SIMPLE_EXECUTION_MODE=jit simple lint <file>

That pre-existing escape hatch takes the same route (`should_prefer_interpreter_for_source`
returns early when the variable is set) and reproduces every number below. It is
the right tool for a *census*, whose question is "which files fail to parse" —
PARSE001 behaves identically under both engines (verified) — and the wrong tool
for a gate that trusts warning counts.

**TODO(lint,P1): make the JIT route the default for `lint_entry.spl` once the
MODINIT001 divergence below is closed. The driver patch and its tests are
described here; the blocker is the engine, not the routing.**

### After — same fixtures, same instrument

| target | lines | interpreted (before) | JIT (after) | speedup |
|---|---|---|---|---|
| 3-line fixture | 3 | 6.66 s | 7.80 s | 0.85x |
| `src/app/coverage/main.spl` | 248 | 99.86 s | 8.36 s | **11.9x** |
| `src/app/io/_CliCommands/run_commands.spl` | 709 | 297.26 s | see A/B below | — |

The shape is what matters: per-file cost went from `~5.5 s + 0.4 s/line` to a
**flat ~8 s**, independent of target size. Small files pay ~1 s more (JIT compile
of the lint app's own module graph); everything else collapses. Peak RSS is
unchanged (~350 MB either way).

### The remaining cost is a fixed per-process floor, and it now dominates

~8 s of every run is compiling the lint app's own module graph from `.spl`
source. There is no compiled-app cache in the driver (`grep` for
`SIMPLE_APP_CACHE`/`app_cache` in `driver/src/`: 0 hits), so it is paid on every
invocation. At ~8 s/file, 31,998 files is ~71 h single-threaded, ~12 h at 6-way
— against ~90 h before. That unblocks the census but leaves the floor as the
next target.

**TODO(lint,P2): remove the per-process module-graph compile from `simple lint`
— AOT-compile the lint app into the shipped binary, or add a compiled-app cache.
Measured at ~8 s per invocation, it is now 100% of the cost of linting a small
file.**

### Batching is NOT an alternative fix — it crashes (PROVED)

The obvious way to amortise that floor is one process for many files. It does not
work, and this was measured rather than assumed. 200 real repo `.spl` files
(44,923 lines) in a single `simple lint <dir>` process under JIT:

    RC=134 (SIGABRT)   wall 57.48 s   max RSS 1,606,112 KB
    thread 'simple-main' has overflowed its stack
    fatal runtime error: stack overflow, aborting

107 files produced a `Found N error(s)` block before the abort; **no summary line
was ever printed**, so a harness trusting the exit code or the summary would have
scored this as zero findings. This is the same cross-file state accumulation
already recorded above as "8.9 GB RSS after 4,363 files" — the JIT reaches it
sooner and as a stack overflow rather than as RSS growth.

So **one process per file remains mandatory**, and any cross-file parse cache is
contraindicated: the shared parser/AST state that a cache would have to reuse is
exactly the state that is already leaking. The fix above deliberately adds no
cache and no cross-file state, so it cannot join that defect family.

### A/B verification — interpreter vs JIT, one process per file per mode

Harness `ab.shs`: 33 deterministically sampled repo `.spl` files (every 900th of
a sorted list of 33,905, capped at 300 lines), each linted twice — once on the
current interpreter route, once with `SIMPLE_EXECUTION_MODE=jit` — against a
**pristine** checkout of `3807bab68e8` (the three files this change touches were
restored from the origin blob and hash-verified first, so the A/B measures the
route change alone). It asserts `results == inputs` for both modes and diffs the
normalised diagnostic stream. The seed banner and the compiler's `[gc-*]` notes
about the *lint tool's own* module graph are excluded — they are not lint
diagnostics; nothing else is filtered.

**This run was stopped early and is a PARTIAL, not a certified result.** 19 of
the 33 files completed before it was killed to stop starving sibling lanes, so
the harness's own `results == inputs` assertion never ran. Treat the counts below
as a lower bound on divergence, never as a rate. (Per this file's own standing
rule, a partial prefix is not a result — the difference here is that the
conclusion drawn from it is one-directional: a single divergence is enough to
block the route flip, and seven were seen.)

    COMPLETED=19  SAME=12  DIFF=7  INTERP_CRASHED=2
    aggregate wall over those 19: interpreter 522.5 s, JIT 156.0 s (3.35x)

The 3.35x aggregate badly understates the win because the sample was capped at
300 lines to keep the interpreted side affordable; the per-file table above
(11.9x at 248 lines) is the honest shape.

**The two routes do NOT agree.** Divergences came in two distinct shapes, and
only the first is harmless.

Shape 1 — the interpreter crashes and the JIT survives (a strict improvement,
but neither verdict is trustworthy):

`src/compiler_rust/lib/std/src/tooling/misc_commands.spl` (176 lines)

* interpreted: `[stmt_get_tag] OOB idx=149 arena_len=79` then
  `error: semantic: array index out of bounds: index is 149 but length is 79`,
  process dies, **no summary, no verdict, and no `not_linted` count** — the file
  is silently absent from the run.
* JIT: same arena OOB (`idx=158`), survives it, emits 5 warnings and
  `Lint passed: all files clean`.

Both engines hit the same underlying AST-arena defect; they differ only in
whether it is fatal. **Neither verdict is trustworthy for such a file** and this
must not be read as "JIT is correct here" — it is `neither_engine_trustworthy`
again. What it does establish is that the interpreter route has its own
fail-open hole: a crashed lint process produces no diagnostic, no summary and no
NOT-LINTED count, which is precisely the blindness this bug file exists to close.

**TODO(lint,P1): a census harness must treat "process died without a summary" as
a distinct CRASH verdict, not fold it into LINTED or NOT_LINTED. The `ab.shs`
control (`summary line present`) is the minimum bar; `misc_commands.spl` is a
live reproducer.**

#### The blocking divergence: JIT invents MODINIT001 warnings

The second and third divergences are not crashes — they are the JIT reporting a
lint the interpreter does not. On
`src/lib/nogc_sync_mut/test_runner/runner_lifecycle.spl` the JIT emits
`MODINIT001` ("module-level initializer is not a literal") at line 199, which is

    var _heartbeat_interval_ms = 5000  # 5 seconds

an integer literal. The file's only two module-level declarations are `5000` and
`0`; neither should be flagged. The interpreter flags neither. **The JIT warning
is a false positive.**

`check_module_init_literal` is a pure **text** lint — it says so in its own
header ("no AST dependency") and it only ever touches `substring`, `starts_with`,
`ends_with` and character comparisons. So this is a pure-Simple execution
divergence, not an AST or parser problem.

Minimal reproducer, 4 declarations, same binary, same tree, one process each:

    var d1 = 7
    var d2 = 12
    var d3 = 123
    var d4 = 1234

| route | MODINIT001 warnings |
|---|---|
| interpreter (current default) | **0** — correct |
| `SIMPLE_EXECUTION_MODE=jit` | **4** — all four flagged |

and in the real file above, `var _last_heartbeat_time = 0` was **not** flagged
under either route.

That split — every digit flagged except `0` — points at the digit test inside
`_mil_is_numeric_literal`:

    val is_digit = ch >= "0" and ch <= "9"

**INFERRED** (the reproducer is PROVED; the mechanism is not yet isolated): the
JIT evaluates the relational text comparisons `>=` / `<=` on single-character
text as something equivalent to `==`, so only the literal `"0"` satisfies
`ch >= "0"`, every other digit falls through to the loop's `else: return false`,
and the whole numeric literal is misclassified. If that is right, the blast
radius is far wider than one lint: every `a >= b` / `a <= b` on `text` in the
tree is suspect under JIT.

**TODO(compiler,P1): isolate and fix text `>=`/`<=` under the JIT. Reproducer:
`printf 'var d1 = 7\n' > d.spl` then compare `simple lint d.spl` against
`SIMPLE_EXECUTION_MODE=jit simple lint d.spl` — 0 warnings vs 1. Confirm first
whether the primitive really is the text relational compare (write a direct
two-line `text` comparison spec) before assuming the lint is the only victim;
this is the "measure the primitive first" case.**

This one defect is the entire reason the route change is not the default. It is
in the engine, not in lint, and not in the routing patch.

The seven divergent files in the partial run, for whoever picks this up:

    src/compiler_rust/lib/std/src/tooling/misc_commands.spl   (interpreter crashed)
    test/01_unit/compiler/loader/generation_sweeper_spec.spl  (interpreter crashed)
    src/lib/nogc_sync_mut/test_runner/runner_lifecycle.spl
    test/01_unit/app/mcp_unit/mcp_cancellation_spec.spl
    test/01_unit/lib/common/encoding/protobuf_e_spec.spl
    test/01_unit/lib/extended/collections_heap_integration_spec.spl
    test/01_unit/lib/nogc_async_mut/terminal/credential/terminal_credential_facade_spec.spl

The last one is 9 lines long, so the cheapest reproduction of a non-crash
divergence is there, not in the 280-line file.

**TODO(compiler,P1): `[stmt_get_tag] OOB idx=N arena_len=79` on
`src/compiler_rust/lib/std/src/tooling/misc_commands.spl` — the AST statement
arena is indexed past its length during lint's parse, fatally under the
interpreter and non-fatally under the JIT. Reproduce with
`simple lint src/compiler_rust/lib/std/src/tooling/misc_commands.spl`.**

### PARSE001 now carries the real location and reason — DONE

Closes the `TODO(lint,P2)` above.
`src/compiler/10.frontend/core/parser.spl` mirrors the **first** parser error out
through the same process-global env channel `par_had_error_mirror` already uses
(and for the same reason — a module-level `var` written inside the parse call
tree is not visible after control returns across the module boundary). New
`parser_first_error_get()` returns `"<line>:<col>:<message>"`, or `""` when
nothing was recorded. Both error sites (`parser_expect` and `parser_error`) feed
it; first error wins, since later ones are usually cascade noise. It is cleared
at the top of `parse_module_silent_checked`, next to the existing mirror clear.

`entry_and_fixes.spl` uses it for PARSE001's line, column and message suffix, and
falls back to the old `1:0` with the unchanged message when the parser recorded
nothing — so the diagnostic can never be weaker than before. **The `NOT LINTED:`
wording is unchanged and is still the head of the message**; the reason is
appended in parentheses. `not_linted_files` and all seven NOT-LINTED reporting
sites are untouched.

Before:

    <file>:1:0: error[PARSE001]: NOT LINTED: source did not parse - every AST-based lint was skipped for this file

After, on a fixture whose only fault is `val y = = 7` on line 8:

    <file>:8:13: error[PARSE001]: NOT LINTED: source did not parse - every AST-based lint was skipped for this file (unexpected token in expression: = '=')

A census can now group parse failures by cause.

Incidental finding while writing that code: the bare `text[:idx]` slice form
still yields the wrong value here — the first draft used `first_error[:head_sep]`
and got line 1 for an error on line 8, while `first_error[0:head_sep]` on the
same input gives 8. This is the `find()`-plus-`[:idx]` lexer defect resurfacing;
the shipped code uses the explicit `[0:idx]` form and says why.

### Dedupe behaviour preserved

`simple lint <dir> <dir> <dir>/` — the same directory three times, spelled two
ways — emits exactly one summary under **both** the interpreter and the JIT
route, i.e. the target and discovered-file dedupe is unchanged by this work. No
lint rule, no dedupe path and no reporting site was modified.

## Re-test after the JIT text-ordering fix (6469d70eb4e) — one blocker closed, a NEW one found

**Binary:** freshly built `cargo build --release -p simple-driver --bin simple` from
tip `7cabb12ee05` (which has `6469d70eb4e` as an ancestor), sha256 prefix
`d74e84cb0162e039`. This rebuild is not optional: the fix is in Rust codegen
(`codegen/instr/core.rs`), so it lives in the **binary**, not the tree — re-testing
with the old `simple.pre-segv-fix-20260731` would have been vacuous.
Note the build is 57 MB, the known no-LLVM size rather than the ~130 MB canonical
one; that does not affect these results (lint needs the parser and the cranelift
JIT, not LLVM codegen) but no perf number here should be read as the shipped artifact.

### MODINIT001 divergence: CLOSED

The real mechanism was not `>=`-collapsing-to-`==` as this file previously
inferred. Per the fixing lane, JIT text `<` `<=` `>` `>=` compared **heap handle
addresses, not content**; it only looked like `==` because `Eq`/`NotEq` already
had a tag-aware fallback while ordering had none.

Attribution is controlled, not assumed — the old binary was first run against the
**new** tree:

| binary | tree | `digits.spl` MODINIT001 under JIT |
|---|---|---|
| `simple.pre-segv-fix-20260731` (Jul 31) | tip `7cabb12ee05` | **4** (false) |
| rebuilt tip `d74e84cb0162e039` | tip `7cabb12ee05` | **0** |

So the symptom tracked the binary, not lint-source drift, and the disappearance
is attributable to `6469d70eb4e`.

**Guarded against agreement-by-silence.** "Both engines agree" is also satisfied
if the JIT stops reporting anything, so two true-positive controls were added:

| control | expected | interpreter | JIT |
|---|---|---|---|
| `compute()` + `1 + 2` + 2 literals | 2 | **2** (lines 4,5) | **2** (lines 4,5) |
| `[]` + 2 int literals | 1 | **1** | **1** |

The rule still detects real non-literal initializers on both engines; only the
false positives vanished. `src/lib/nogc_sync_mut/test_runner/runner_lifecycle.spl`,
the original reproducer, is now **SAME**.

### Corpus re-test — 10 files, one process per file per mode

`retest.shs`, asserting `results == inputs` for both modes and scoring
MODINIT001 counts separately from the SAME/DIFF verdict.

    INPUTS=10  INTERP_LINTED=8  JIT_LINTED=10  IDENTICAL=4   (harness exit 4)

`modinit_j` is **0 on every file where the interpreter did not crash**. The
remaining divergences are two shapes, neither of them MODINIT001:

* **2 files — the interpreter crashes, the JIT completes** (`misc_commands.spl`,
  `generation_sweeper_spec.spl`). Already filed above as the AST-arena defect.
  On `generation_sweeper_spec.spl` the JIT's 4 MODINIT001 were adjudicated and
  are **true positives**: lines 16/17/146/147 are exactly the `[]` collection
  initializers the rule's own header says to flag, while the integer literals on
  15/18/145 are correctly ignored. The interpreter reported none only because it
  died.
* **4 files — a NEW, independent JIT defect**, below.

### NEW BLOCKER: `text.repeat()` returns the literal text "error" under the JIT

Measured on the primitive directly rather than inferred from the lint:

    fn main() -> i64:
        val s = " ".repeat(4)
        print "LEN={s.len()}"
        print "VAL=[{s}]"
        0

| route | output |
|---|---|
| interpreter | `LEN=4`, `VAL=[    ]` — correct |
| JIT | `Runtime error: Function 'str.repeat' not found`, `LEN=-1`, `VAL=[error]` |

So `.repeat()` on text does not merely fail loudly — it **substitutes the string
`"error"`** and reports length -1. This is the whole content of the four
remaining diffs.

**Why this blocks the route change specifically.** `" ".repeat(n)` is how
`src/lib/nogc_sync_mut/tooling/easy_fix/rules_lint.spl` builds the *indentation
of EasyFix replacement text* (7 call sites). `simple fix` and `simple fmt`
dispatch through the **same** `src/app/cli/lint_entry.spl` as `simple lint`, so
the exemption cannot be granted to lint alone — flipping it puts `fix` on the
JIT route too, where it would write `error` where indentation belongs.
Demonstrated end-to-end on a non-exhaustive-match fixture:

    simple fix --dry-run <fixture>
      interpreter: (no runtime errors)
      JIT:         Runtime error: Function 'str.repeat' not found   x2

on the very rule (`non_exhaustive_match`) whose replacement text is built with
`" ".repeat(indent)`.

**TODO(compiler,P1): `text.repeat(n)` is unresolved under the JIT and yields the
literal text "error" with len -1 instead of the repeated string. Reproducer is
the five-line probe above — `simple run` it with `SIMPLE_EXECUTION_MODE=interpret`
vs `=jit`. Blast radius is every `.repeat()` on text, not just lint; the reason it
surfaces here is that `easy_fix/rules_lint.spl` uses it to indent generated fixes.**

### Status of the route change: still written, still NOT landed

The driver patch (`is_jit_safe_cli_args_entrypoint`) is unchanged and its three
unit tests still accompany the ten pre-existing `exec_core` tests. The MODINIT001
objection is gone; the `.repeat()` objection is new and is a strictly harder one,
because it can corrupt files that `simple fix` writes rather than only adding a
spurious warning.

**TODO(lint,P1): land the JIT route for `lint_entry.spl` once `text.repeat()` is
fixed under the JIT. At that point re-run `retest.shs` and require
`INTERP_LINTED == JIT_LINTED == IDENTICAL == INPUTS`, with the two MODINIT001
true-positive controls still firing 2/2 and 1/1.**

`SIMPLE_EXECUTION_MODE=jit` remains correct for a **census**, whose question is
which files fail to parse: PARSE001 agrees across both engines, and the
`.repeat()` defect only adds noise lines and corrupts *fix* text, which a census
never applies.

## CRASH verdict — LANDED. "Died without a summary" is now a countable outcome

**TODO(lint,P1): a census harness must treat "process died without a summary" as
a distinct CRASH verdict** — **DONE**, as
`scripts/check/check-lint-census.shs`.

The NOT-LINTED work above closes the case where lint *runs* and cannot parse a
file. It cannot close the case where lint **dies**, because nothing in a dead
process gets to report anything. Both holes are fail-open in the same direction:
a sweep that scores by summary lines sees a crashed file as absent rather than
failed, and a sweep that scores by "files that produced no complaint" sees it as
clean.

The harness gives every file exactly one of four verdicts and never a bucket
called "checked":

| verdict | meaning |
|---|---|
| `LINTED` | analysed; lint reported a summary |
| `NOT_LINTED` | lint ran, could not parse the file, and said so |
| `CRASH` | the process ended without emitting a summary line |
| `TIMEOUT` | the process exceeded the per-file budget |

`CRASH` and `TIMEOUT` are failures of the *instrument*, not verdicts about the
file, and are counted separately so a clean census cannot quietly have lost
files. Exit 0 requires every file to be `LINTED` or `NOT_LINTED`; any `CRASH` or
`TIMEOUT` exits 1; any harness fault exits 2. One process per file, per the
batching evidence already recorded in this file. The run asserts
`verdicts == inputs` and ERRORs otherwise, so a harness that dies partway cannot
be mistaken for a completed census.

### Non-vacuity — PROVED by sabotage, not asserted

Per this file's own standing rule, a count-based check cannot detect selective
blindness, so the classifier is exercised directly:

    sh scripts/check/check-lint-census.shs --self-test

`--self-test` feeds the **same `classify_run`** the census calls (not a copy)
synthetic lint output for all four outcomes, including the two shapes that
matter most: a crash that still exits 0, and a run that emitted real warnings
and then died — the case a summary-line-counting sweep gets wrong.

RED: `classify_run` gutted to an unconditional `echo "LINTED"; return`

    FAIL  not_linted_json -> LINTED (expected NOT_LINTED)
    FAIL  crash_arena_oob -> LINTED (expected CRASH)
    FAIL  crash_rc_zero -> LINTED (expected CRASH)
    FAIL  crash_after_findings -> LINTED (expected CRASH)
    FAIL  timeout_124 -> LINTED (expected TIMEOUT)
    ...
    FAIL: self-test 9 of 11 classifier cases wrong        (exit 1)

GREEN: implementation restored, byte-identical to the committed file

    PASS: self-test 11 of 11 classifier cases correct     (exit 0)

Gutting the implementation flips 9 of 11 cases. This oracle fails when
sabotaged, which is the precondition the retracted census failed.

### Live end-to-end run — the reproducer scores CRASH, a live control scores LINTED

Not just synthetic. Binary
`bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`, tree = a
private `git archive` of origin `5ca84bcefe5`, never the shared working copy.
Two real files in one census, the live reproducer plus a positive control:

    census: inputs=2 verdicts=2 linted=1 not_linted=0 crash=1 timeout=0
    --- files with no verdict of their own ---
    CRASH   src/compiler_rust/lib/std/src/tooling/misc_commands.spl   rc=1
    FAIL: 1 file(s) crashed and 0 timed out without producing a lint
    summary; they are NOT checked files                   (exit 1)

The control (`LINTED`, rc=0) in the same session rules out a harness that simply
fails everything. Before this, that same run through the plain CLI produced
**zero** summary lines and the file was absent from the tally entirely.

### What this does NOT do

It does not make a crashed file's *content* verified — a `CRASH` file has been
analysed **less** than a `NOT_LINTED` one. It does not lower the per-file lint
cost, so a repo-wide census is still governed by the throughput numbers above.
And it is a harness, not a gate: nothing yet runs it in CI.

**TODO(lint,P2): wire `check-lint-census.shs` into the repo verification layer
so a crashed lint file fails a gate rather than only a manual sweep. Until then
this is opt-in, and `repo_verification_layer_is_fail_open_2026-07-28.md` still
applies.**

## The interpreter CRASH on misc_commands.spl — CONTAINED (not root-caused)

**Reproduced and fixed 2026-08-01.** Instrument:
`bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731` (Jul 30),
tree = a private `git archive` of origin `5ca84bcefe5`, never the shared working
copy. One process per file throughout.

### RED — measured, both engines, same file, same binary

`simple lint src/compiler_rust/lib/std/src/tooling/misc_commands.spl`

Interpreter route (the default — `lint_entry.spl` mentions `get_cli_args`, so
`should_prefer_interpreter_for_source` routes it to the interpreter; no
`[jit-fallback]` marker fires because it is a deliberate pre-JIT decision):

    [stmt_get_tag] OOB idx=149 arena_len=79 arena_gen=1 -> -1
    error: semantic: array index out of bounds: index is 149 but length is 79
    rc=1, summary lines: 0

`SIMPLE_EXECUTION_MODE=jit`, same file, same binary:

    [stmt_get_tag] OOB idx=149 arena_len=79 arena_gen=1 -> -1
    [stmt_get_tag] OOB idx=158 arena_len=79 arena_gen=1 -> -1
    ... 5 warnings ...
    Found 0 error(s), 5 warning(s), 0 auto-fix(es) available
    Lint passed: all files clean
    rc=0

### The mechanism: the guard was on the dispatcher, not on its siblings

The two lines above are one line apart and carry the **same index and the same
length**. `stmt_get_tag` bounds-checks, prints, and returns -1; the walker takes
its default branch and then reads the SAME stale index through
`stmt_get_span/expr/name/type/body`, none of which were bounds-checked. That
unguarded read is what killed the process.

Earlier lanes guarded `decl_get`, `expr_contains_yield`, `stmt_contains_yield`,
`expr_get_tag` and `stmt_get_tag` — the dispatchers and the recursive walkers —
and left every plain field accessor in the same two arenas unguarded. This is
the "a sweep that does not enumerate the family leaves siblings" shape.

Fixed by completing the family, as pure additions (55 + 63 + 13 + 15 lines
added, **0 lines removed**):

* `src/compiler/10.frontend/core/ast_stmt.spl` — `stmt_get_span`,
  `stmt_get_expr`, `stmt_get_name`, `stmt_get_type`, `stmt_get_body`
* `src/compiler/10.frontend/core/_AstExpr/accessors.spl` — `expr_get_span`,
  `_int`, `_float`, `_str`, `_left`, `_right`, `_extra`, `_args`, `_arg_names`,
  `_stmts`
* `src/compiler/10.frontend/core/_Ast/module_state.spl` — the two struct
  builders `expr_get` and `stmt_get`, which read eleven and seven arena arrays
  respectively and are the widest single crash surfaces in the family

Neutral returns match the precedent already set by `decl_get` (-1 / "" / 0 /
`[]`, and tag 0 for the struct builders, since no real `EXPR_*` or `STMT_*`
constant is 0). The loud, always-on OOB line stays on `stmt_get_tag` /
`expr_get_tag`, which any walk reaching a stale node passes through first, so
the diagnosis is not silenced. The new per-accessor line is gated behind
`SIMPLE_TRACE_AST_OOB` (default off) so a walk over a stale subtree cannot flood
the output with one line per field.

### GREEN — same census, same binary, same tree, patched

    census: inputs=2 verdicts=2 linted=2 not_linted=0 crash=0 timeout=0
    PASS: 2 file(s) all produced a lint summary (2 linted, 0 not linted)
    LINTED  lane_probe/clean_control.spl                                rc=0
    LINTED  src/compiler_rust/lib/std/src/tooling/misc_commands.spl     rc=0

against the identical RED census on the identical tree before the patch:

    census: inputs=2 verdicts=2 linted=1 not_linted=0 crash=1 timeout=0
    CRASH   src/compiler_rust/lib/std/src/tooling/misc_commands.spl     rc=1

The positive control is `LINTED` in **both** runs, so the change did not simply
make everything pass. The three edited files are themselves compiled as part of
the lint tool's own module graph on every one of these runs, so a GREEN census
is also a compile check of the edit.

### This is CONTAINMENT, and the root cause is STILL OPEN

**Do not read this as "the arena desync is fixed."** What is fixed is that the
interpreter now reports instead of dying. The stale index is still stale, and a
walk that touches it still gets neutral data rather than the real node, so:

* **Neither engine's verdict on such a file is trustworthy.** The JIT's
  `Lint passed: all files clean` was never evidence the file is clean; it is
  evidence the JIT survived the same corruption. `neither_engine_trustworthy`
  applies to both sides here.
* The five warnings the JIT reports and the warnings the interpreter now reports
  after this change are computed over a partly-neutral AST.

The unexplained part is specific and should be the next question asked:
**`arena_gen=1`**. The generation counter is bumped by `ast_reset()` before it
clears, so a stale index minted in a previous compilation unit would report a
generation ahead of the one it was minted in. At generation 1 no second
`ast_reset()` has run, so this index did not survive a reset — the mechanism
that the guards on `stmt_get_tag`, `expr_contains_yield` and `decl_get` were all
written for does not explain this instance. Candidate explanations not yet
distinguished: an index from a different arena (a decl or expr id used as a stmt
id), an arena cleared without the generation being bumped, or two live copies of
the `compiler.core.ast_stmt` module state under different module spellings.

**TODO(compiler,P1): explain how a stmt index of 149 reaches an accessor while
the live stmt arena holds 79 entries at `arena_gen=1`, i.e. with no intervening
`ast_reset()`. Reproducer: `simple lint
src/compiler_rust/lib/std/src/tooling/misc_commands.spl` with
`SIMPLE_TRACE_AST_OOB=1`; the guards added above name the exact accessor that
receives the stale index. Until this is answered, lint results for any file that
prints an arena OOB line must be treated as unverified on BOTH engines.**

### Incidental, unrelated to the OOB, seen in the same runs

`Runtime error: Function 'str.repeat' not found` printed six times in the JIT
run — the same `text.repeat()` defect already recorded above, reached here
through the easy-fix indenter. It does not affect the crash or its fix.
