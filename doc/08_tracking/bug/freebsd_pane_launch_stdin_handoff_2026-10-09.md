# FreeBSD pane launch consumes the first command

## Reproduction and scope

The unchanged `test/01_unit/app/llm_caret/pane_backend_spec.spl` executed all
15 examples on the admitted FreeBSD bootstrap diagnostic producer. Fourteen
passed; the live-shell example captured only `#` instead of the computed
`14133`. The containment guard returned exit 1 with quiescence confirmed.
Production pane, smux API and PTY facade sources were identical at `73a097bb`
and the fix's release base `b05fbaa6a1b`.

A single-example diagnostic retained the original assertions and observed a
shell prompt before sending. It passed after approximately 123 ms between
spawn return and send. This supports an input race across the interactive
launcher shell's `exec` handoff. The prompt does not distinguish the launcher
from the target shell, so the diagnostic alone does not identify the exact
shell read-ahead or terminal-flush operation.

## Correction

The POSIX PTY API accepts an executable path without arguments. The backend
previously started an interactive `/bin/sh`, wrote its launch command to the
PTY, and returned before that handoff completed. The backend now writes a
one-shot script in a fresh private 0700 directory and starts that executable.
The script reads its own file rather than terminal input. It removes its file
and directory, then executes the existing quoted `env` command. Literal argv,
TMUX variable removal, `TERM=xterm-256color` and stderr redirection retain
their previous construction. No prompt heuristic or startup delay is added.

The parent removes the private artifacts on preparation/spawn failure and on
pane close, including close before the child has opened the script. Removal
is limited to the known launch file and its empty private directory. The
Windows command-line path and the tmux backend retain their existing behavior.

## Verification and boundary

The canonical 15-example test remains unchanged. The explicit POSIX fixture
`test/fixtures/llm_caret/pane_posix_launch_probe.spl` adds real checks for
immediate command delivery, quoted argv, child environment, quoted stderr
paths, normal self-cleanup, failed executable cleanup, immediate pane close
and refusal of an unusable temporary parent.

Focused FreeBSD validation passed on 2026-10-09:

| Run | Executed | Passed | Failed / skipped / dropped | Duration |
| --- | ---: | ---: | --- | ---: |
| Unchanged original spec | 15 | 15 | 0 / 0 / 0 | 1,135 ms |
| POSIX regression fixture | 3 | 3 | 0 / 0 / 0 | 1,248 ms |

The two test processes ran concurrently under the admitted containment guard.
Both test processes and the guard returned exit 0, quiescence was 1, retained
processes were 0, and observed peak aggregate RSS was 1,841,472 KiB against a
5,859,375 KiB cap. These observations cover this focused run; they are not a
whole-suite PASS or a memory/performance acceptance claim. The earlier
11.8-second failure included the assertion's polling timeout, so comparison
with the successful run is not a controlled performance benchmark.

The tested source base was
`b05fbaa6a1b4f9d9918f62af297d18d25eb9f07b`. SHA-256 pins:

- Production `pane_backend.spl`:
  `f6e4c898f52199e679a8016cfc456329ceaf89a9ecf2e6cd14465a4056231f36`
- New `pane_posix_launch_probe.spl`:
  `ac56750ae53523a76497d335ed4008707d1b870b7926638cd1a672145a26c04f`
- Unchanged `pane_backend_spec.spl`:
  `ed09604a3e52bcdb24057cff9c3f5ca8592b80e99df9885ff640451a86ac3ac6`
- Admitted FreeBSD bootstrap diagnostic producer:
  `daadf4c854c0ef8d5a0d9cf33379c3dd28a1f7ba7c93a6b915c77973943fb721`

The local evidence is retained under
`build/pane-handoff-diagnostic/final-evidence/`, including `request.json`,
`test-exits.json`, the guard receipt and `verified-results.json`. The production
and fixture hashes remained unchanged after testing. Static `git diff --check`
and both working/staged direct-environment runtime guards passed.

The producer warns that it is a Rust-built bootstrap seed, not the normal
Simple tool. This is Phase 1 diagnostic evidence only; the pure-Simple CLI has
not been admitted by this run. The new fixture uses a single-symbol spec import
because the admitted producer predates grouped-import fix #2718; the canonical
spec was not rewritten to work around that producer limitation.

The temporary parent follows `TMPDIR`, defaulting to `/tmp`, and must be an
absolute path on a filesystem that permits execution. There is no fallback
that defeats a `noexec` mount. The current PTY primitive reports the fork PID
before executable admission, so a `noexec` failure can first appear as a child
exit; explicit pane close removes remaining launch artifacts. An argv-taking
PTY API with exec-error reporting would remove this limitation but is outside
this pure-Simple correction. The bootstrap producer is diagnostic evidence,
not an admitted replacement for the unavailable pure-Simple CLI.
