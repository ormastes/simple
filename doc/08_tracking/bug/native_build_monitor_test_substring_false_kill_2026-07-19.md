# Native build monitor test-substring false kill

**Status:** OPEN  
**Severity:** P1 — a healthy incremental build was terminated as a hung test

## Reproduction

A strict targeted native build whose entry is
`src/app/test_runner_new/main.spl` was terminated with exit 143. The resource
monitor log recorded a kill after 67 seconds at 996% CPU.

## Root cause

The monitor classifies the complete argv with a broad
`*bin/simple*test*` glob. The `test_runner_new` entry substring therefore makes
an unrelated `simple native-build` look like `simple test`.

## Root solution

Classify the actual subcommand token instead of substring-matching all argv.
Add a monitor contract covering `simple test` as positive and
`simple native-build ... test_runner_new ...` as negative before retrying the
cached Stage 4 build.
