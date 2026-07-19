# Native build monitor test-substring false kill

**Status:** SOURCE FIXED
**Severity:** P1 — a healthy incremental build was terminated as a hung test

## Reproduction

A strict targeted native build whose entry is
`src/app/test_runner_new/main.spl` was terminated with exit 143. The resource
monitor log recorded a kill after 67 seconds at 996% CPU.

## Root cause

The monitor classifies the complete argv with a broad
`*bin/simple*test*` glob. The `test_runner_new` entry substring therefore makes
an unrelated `simple native-build` look like `simple test`.

## Solution

The monitor now recognizes adjacent `<.../simple> <run|test>` tokens instead
of searching arbitrary argv substrings. Its decision-matrix check covers a
wrapped real test as positive and
`simple native-build ... test_runner_new ...` as negative.

## Evidence

`sh scripts/resource/kill_simple_monitor_test.shs`: PASS. The monitor still
kills the calibrated test CPU/RSS runaways and spares native-build, healthy,
young, protected, and root-owned rows.
