# macOS test-runner RSS qualification fails before executing tests

- Date: 2026-09-21
- Severity: P1 — platform qualification blocker
- Status: FIXED — focused harness regression verified on macOS arm64
- Scope: `scripts/check/check-test-runner-rss-batch.shs`

## Reproduction and cause

The batch RSS gate uses `/usr/bin/time -f %M -o ...` unconditionally. Apple
`time` exists and passes the prerequisite check, but rejects GNU `-f` before
starting `bin/simple test`. Compiler/interpreter directory-test qualification
therefore cannot reach its worker, example-count, or memory assertions on macOS.

Running the script from base `17883250f21` with `TEST_RUNNER_RSS_FILE_COUNT=1`
and a temporary result directory produced:

```text
error=runner_failed:1
/usr/bin/time: illegal option -- f
usage: time [-al] [-h | -p] [-o file] utility [argument ...]
```

## Fix

On Darwin, invoke Apple `time -l -o` and convert its maximum resident set size
from bytes to KiB, rounding up. Keep timing output separate from runner stderr
and reject an absent, nonnumeric, or zero measurement. Other platforms retain
the GNU `%M` path. Select `gtimeout` when Homebrew exposes only its prefixed
command name; a timeout utility remains an explicit prerequisite.

## Verification

`sh scripts/test/test-runner-rss-platform.shs` passed on macOS arm64. The
regression executes the actual platform time utility around a controlled runner
and checks three fixture files, two batch workers, six examples, nonzero RSS,
exact byte-to-KiB conversion, isolation from misleading stderr, rejection of a
1 KiB budget, and propagation of runner exit 7.

Both `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`
passed. `git diff --check` passed before this report was added.

This is harness verification, not a compiler memory qualification result. No
deployed compiler was rebuilt or measured, and the GNU branch was not executed
on this macOS host.
