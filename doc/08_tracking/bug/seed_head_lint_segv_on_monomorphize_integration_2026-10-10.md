# BUG-IT-7 (tooling) — seed-head `lint` crashes (rc=139) on `src/compiler/40.mono/monomorphize_integration.spl`

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests.

Binary `C:/dev/simple-bootstrap-storage/seed-head/simple.exe` (sha256 278e9d1137..., built 2026-10-10
05:33), Windows 11. `simple.exe lint src/compiler/40.mono/monomorphize_integration.spl` exits 139
after ~205 s with no verdict line, on release/1.0 @ b68c0c65708 (edited file) AND @ 6b540f21546
(`C:/dev/simple-rel-ladder`, pristine file) — a linter defect on this input (1.8k lines, heavy
`match`), not a source problem. The 40.mono change in this lane was therefore verified by execution
(probe + 8 mono specs under the seed-head runner) instead of lint. Not investigated further here.
