# MCP native probe admitted nonzero exits — 2026-07-23

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
