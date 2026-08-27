# MCP core tool set serves 3 tools while its specs require 20

**Date:** 2026-08-25 · **Severity:** MEDIUM (core/auto MCP mode advertises far fewer tools than specified) · **Status:** OPEN · **Pre-existing at origin**

## Symptom
`test/01_unit/app/mcp/mcp_tool_set_spec.spl` and `mcp_dynload_upgrade_spec.spl`
fail with `expected 3 to equal 20`: the core (pre-upgrade) tool list served in
`auto`/`core` mode contains 3 names, while both specs pin 20.

## Evidence it is not caused by the caret tools
Measured 2026-08-25 on the deployed seed (60641352 B, 05:16) by stashing the
caret changes: at origin content the same two specs fail identically on the
core-count example, and the FULL-list pin was itself already stale (origin
serves 154 against a pin of 151). The caret `caret_*` group adds exactly 9,
so the full pin was updated 151 -> 163; the core-count failure is untouched
by that change and reproduces without it.

## Fix direction
Decide which side is authoritative: either the core list should really carry
the 20 documented tools (restore the missing 17 names to the core selector in
`src/app/mcp/main_static_tools.spl` / the core-set filter), or the
specification changed and both specs' `20` pins are stale. Do NOT "fix" this
by editing the pin without establishing which set the product is supposed to
serve — the full-list pin was already drifting for the same reason.

## Unblock condition
`mcp_tool_set_spec` and `mcp_dynload_upgrade_spec` report 0 failed with a core
count that matches a stated requirement, and the full-list pin is regenerated
from the table rather than hand-maintained.
