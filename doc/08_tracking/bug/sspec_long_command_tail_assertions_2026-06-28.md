# SSpec Long Command Tail Assertions May Be Skipped

## Closed 2026-09-13 — root cause (matcher clearing a prior failure) is fixed; tail assertions are now observed

- **measured** Binary: Rust seed `bin/simple` v1.0.0-rc.1 (16,347,136 bytes, 2026-09-02), Windows host.
- **measured** The minimized repro of the shared root cause (`sspec_matcher_success_clears_prior_failure_2026-06-28`) — a failing `expect` followed by a passing one in the same `it` — now reports `1 example, 1 failure` / `outcome=ERROR`, i.e. the later assertion no longer erases the earlier failure.
- **measured** A single example containing a passing assertion followed by a genuinely failing one prints `1 example, 1 failure`, so a trailing assertion is still evaluated and counted.
- **inferred** The original GUI RenderDoc autodiscovery symptom was attributed in the sibling entry to that same matcher-clear defect, not to command length.

Date: 2026-06-28
Status: closed (fixed) 2026-09-13
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
