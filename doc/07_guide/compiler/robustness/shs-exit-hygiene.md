# Shell exit-status hygiene scan (advisory)

Robustness item 15a, script half. A script that reads `tail`'s status after a
pipe, `echo`'s after a report line, or never looks at a `timeout` status
reports a failed or killed compiler as green.

Scanner: `scripts/check/lib/shs-pipe-exit-hygiene.shs`.
It is **advisory everywhere**. It never changes a required verdict.

## Rules

| rule | reported shape | write instead |
|---|---|---|
| `PIPE-STATUS` | a bare `cmd \| tail\|head\|tee\|cat` immediately followed by a direct `$?` read (`rc=$?`, `[ $? ...`, `test $?`, `exit $?`, `return $?`, `case $? in`) | `cmd >log 2>&1; rc=$?; tail log` · `set -o pipefail` · `PIPESTATUS` |
| `TIMEOUT-UNCHECKED` | a bare `timeout ... cmd` statement followed by an echo/printf saying PASS/OK/passed/success | `timeout ...; rc=$?` and test it · `if timeout ...; then` |
| `STALE-RC` | a direct `$?` read right after `echo`/`printf`/`sleep`/`date`/`rm -f`, or after `local\|export\|readonly\|declare\|typeset v=$(cmd)` | `cmd; rc=$?` first, report afterwards |

Deliberately **not** reported, because the scanner cannot know the filter's
status was unintended: any file mentioning `pipefail`; `PIPESTATUS`; `&&`/`||`
on the pipeline; `x=$(a | b) || ...`; a last stage of grep/sort/cut/tr/sed/wc;
a left side of echo/printf/cat or the end of a group (`} 2>&1 | tee log`);
`if ...; then ...; else rc=$?`; `f() { rc=$?; ... }`; `timeout ... || true`;
`timeout` under `set -e`; case patterns. Each is a must-not-flag fixture.

A reviewed line is exempted with a trailing `# exit-hygiene-ok: <reason>`.

## Where it reports

- **Range gate** `check-range-shs-hygiene-push.shs` (required): for each
  `scripts/**.sh|.shs` the range touches, findings that are new versus the base
  blob are printed on **stderr** as
  `NOTE (advisory, verdict unaffected) — ...`. The verdict line, the exit code
  and the 16-fixture pre-scan selftest are unchanged; the scan is switched off
  while that selftest runs, and a range touching no script does no extra work.
- **Tree census** (not a push row):

  ```sh
  sh scripts/check/check-range-shs-hygiene-push.shs --tree [--rev <rev>]
  sh scripts/check/check-range-shs-hygiene-push.shs --tree --generate-baseline   # reviewed updates only
  ```

  Committed content of `<rev>` (default `HEAD`) against the shrink-only
  baseline `scripts/check/shs_pipe_exit_hygiene_baseline.txt`
  (`count<TAB>rule<TAB>path`). A row above its baseline fails, and so does a
  stale row the tree no longer needs. About a minute for ~2,400 scripts.
- **Extended CI job** (`code-idiom-gates.yml`, non-required): the library
  selftest and the tree census.

## Selftest and adding a case

```sh
sh scripts/check/lib/shs-pipe-exit-hygiene.shs --selftest
```

43 fixtures: 8 must-flag, 27 must-not-flag (including the 20 legitimate shapes
from the 2026-10-10 review), 5 tree-census cases, 3 proving the range gate
stays advisory. To add a rule or a shape, edit `analyze()` and add an `_hx`
fixture for both directions; the selftest asserts the rule-fixture count.

## Switch

There is no blocking mode. To silence the NOTE for one line use the
`exit-hygiene-ok` marker; removing the library file removes the NOTE (the range
gate treats the library as optional) and makes `--tree` an ERROR.

## Known limits

- Statement heuristic, not a shell parser: it under-reports. A status lost
  through `if cmd | tail; then`, `x=$(cmd | head) || die`, a function boundary,
  `eval`, or a multi-line `( ... )` group is not seen.
- `pipefail` anywhere in a file silences `PIPE-STATUS` for the whole file, even
  if it is set after the pipeline or only in a subshell.
- A file whose quoting it cannot balance is reported as `SCAN-INCOMPLETE`
  (counted in the tree verdict, never a failure).
- Nothing blocks: a new offender lands with a NOTE the author may not read.
