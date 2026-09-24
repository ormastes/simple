<!-- codex-design -->
# DevHub mode verification plan

Run `sh test/00_unit/scripts/devhub_windows_launch_modes_test.shs` for the
POSIX wrapper contract and `powershell -NoProfile -ExecutionPolicy Bypass -File
test/00_unit/scripts/devhub_windows_launcher_test.ps1` for Windows native
dispatch, argument/exit propagation, explicit POSIX compatibility, and
absence-of-probe markers. Inspect the wrapper diff for REQ-DHLM-005 (no AV
operations). Native Windows tests deliberately remove `sh.exe` from PATH while
retaining `certutil` for receipt hashing.

Outstanding: actual loader design/implementation, native loading behavior,
and independent classification of the exact reported Wacatac artifact.
