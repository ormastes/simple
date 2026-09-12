# SSpec Long Command Tail Assertions May Be Skipped

Date: 2026-06-28
Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
