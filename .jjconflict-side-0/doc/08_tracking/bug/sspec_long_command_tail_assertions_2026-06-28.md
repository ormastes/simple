# SSpec Long Command Tail Assertions May Be Skipped

Date: 2026-06-28
Status: open
Owner: test-runner

## Summary

`test/03_system/check/gui_renderdoc_aggregate_autodiscovery_spec.spl` can report
`3 examples, 0 failures` even when assertions after the long third scenario
command should fail.

## Reproduction

1. Copy the autodiscovery spec to a fresh build path.
2. Insert `expect("deliberate").to_equal("failure")` immediately after:
   `step("Assert newest canonical wrapper evidence wins over stale current refresh evidence")`.
3. Run:
   `SIMPLE_LIB=src bin/simple test build/tmp-sspec-check/gui_renderdoc_aggregate_autodiscovery_deliberate_fail_spec.spl --mode=interpreter --fail-fast`

Observed result: the copied spec still reports all examples passing.

## Impact

Assertions after very long command construction can be skipped or otherwise not
observed by the SSpec runner. For GUI evidence specs, this can let stale or
incomplete aggregate evidence appear green even when generated `evidence.env`
rows show retained 4K/8K status failures.

## Current Mitigation

For long-command GUI evidence scenarios, put critical evidence checks into the
shell command itself with `grep -qx ... && ...`, then assert the command exit
code. Prefer splitting long setup commands into shorter helper scripts or
scenario helpers before relying on post-command assertions.
