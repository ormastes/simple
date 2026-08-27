# MCP core tool set serves 3 tools while its specs require 20

**Date:** 2026-08-25 · **Severity:** MEDIUM (core/auto MCP mode advertises far fewer tools than specified) · **Status:** FIXED 2026-08-26 · **Pre-existing at origin**

## Resolution (2026-08-26)
The product side was authoritative-wrong, not the specs. `git log -S` shows
`_mcp_core_tool_names` was BORN with 3 names at `cfe0506e336` (2026-08-05) and
was never 20 — the only 3↔0 flips in its history are the known
`6f86ff32a7d` tree wipe and its `ae55a746719` restore, so this is not a
stale-snapshot clobber. The binding contract in
`doc/03_plan/app/mcp/mcp_core_default_dynload_plan_2026-06-13.md` states
"core (20 tools)", and task B4 of the startup-perf plan says "core ~15-25
tools", so the implementation never met its spec. `_mcp_core_tool_names` in
`src/app/mcp/main_static_tools.spl` now returns the 20 everyday dev tools
(read/navigate, write, build/verify, vcs), keeping the original three and
adding the names the specs pin by hand (`simple_read`, `simple_check`,
`simple_edit`, `simple_run`, `simple_test`, `simple_commit`). No `debug_*`,
`play_*` or `assistant_*` tool is in the core set; dispatch stays unfiltered.

The stale FULL-list pins in `mcp_static_tools_perf_spec.spl` were also
re-measured (151 -> 163 tools, 38114 -> 45397 chars). **The second half of the
unblock condition is NOT met:** that pin is still hand-maintained, not
regenerated from the table. The only guard against it drifting again is that
`mcp_tool_set_spec.spl` pins the same 163 independently, so a single-sided
edit turns one of the two red. Regenerating the pin from
`_mcp_static_tool_table()` remains open.

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
