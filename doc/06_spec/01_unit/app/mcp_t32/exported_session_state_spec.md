# MCP T32 exported session state

Hand-maintained companion to `test/01_unit/app/mcp_t32/exported_session_state_spec.spl`.
SSpec execution status: UNEXECUTED. Separate native fixture: 18 assertions PASS.

The scenario saves all six state values, writes nondefault values through the
real imported owner declarations, asserts the two collection lengths, current
session, current core, area readiness and area name, then restores saved state.
It neither launches TRACE32 nor communicates with a process/device.

The separate native fixture uses independent writer and reader modules to
verify eighteen predicates across defaults, populated state and reset state.
Baseline native compilation reproduced the private-static rejection. Fixed
native build/run both exited 0 with quiescent receipts and printed eighteen
PASS results (defaults, populated values, reset). Evidence and exact hashes are
in `doc/08_tracking/bug/mcp_t32_exported_static_visibility_2026_11_06.md`.
Broader MCP and SSpec runner gates remain pending.
