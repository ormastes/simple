<!-- codex-design -->
# DevHub mode verification plan

Run `sh test/00_unit/scripts/devhub_windows_launch_modes_test.shs` for
REQ-DHLM-001 through REQ-DHLM-004, using process dispatch and absence-of-probe
markers. Inspect the small wrapper diff for REQ-DHLM-005 (no AV operations).
Run the existing Windows launcher PowerShell test for transport regression.
The nonexistent PowerShell mode test referenced by the interrupted lane is
replaced by this implemented shell harness, runnable under Git for Windows.

Outstanding: actual loader design/implementation, native loading behavior,
and independent classification of the exact reported Wacatac artifact.
