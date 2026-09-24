# MCP native probe admitted nonzero exits — 2026-07-23
## Closed 2026-09-16 — Status FIXED; probe exit status now enforced, adversarial contract added

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** FIXED

## Reproduction

A hash-valid native server could print the expected `tools/list` and
`simple_pipe` response frames, then exit 1. The setup wrapper ignored that exit
and wrote its probe-admission stamp.

## Root cause and fix

`mcp_probe_native` used `probe_timeout ... || true` and validated stdout only.
It now captures the probe status and requires zero before validating frames or
writing the stamp, matching the LSP wrapper. The adversarial wrapper contract
emits valid frames, exits 1, and asserts that no admission stamp exists.

