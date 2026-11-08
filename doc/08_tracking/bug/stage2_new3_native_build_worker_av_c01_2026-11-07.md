# stage2_new3 native-build worker AV on c01 (2026-11-07)

**Status:** open, P1. Blocks retiring the frozen stage2.

## Repro
- Binary: `C:/dev/p3new/stage2new/stage2_new3.exe` (26,523,136 B, built 2026-11-07 17:32). Built from
  `7fdd36aa490` + #7506 + #7541 + the workaround-removal commit `0bccd872d15`, with the
  64 MiB stack patch.
- Command: `pwsh C:/dev/p3new/s3sanity/run_case_s2new_mf8.ps1 -Name c01 -Bin <stage2_new3.exe>`
- Result: parse, HIR, AOP weave and native_cache all finish. Then:
  `phase=native_compile current=test.s3sanity.c01` ->
  `native-build worker terminated with Windows native status 0xC0000005 (access violation)`.
  bootstrap-error-count is 0 at every point. No `rejected invalid array handle` line is printed.
  hello fails the same way; var produced no log.
- Earlier evidence: `stage2_new.exe` (rebuild #1) AV'd on c01 after `rejected invalid array handle`,
  root-caused and fixed in #7541. This AV is a new site, in codegen/native_compile.

## Unknowns
- Whether the AV comes from the workaround removal (`0bccd872d15`). That needs a rebuild without it,
  which is deferred per the owner (minimise phase-2 rebuilds).
- No lldb backtrace yet.

## Decision
Phase 2 rebuilds are paused. Phase 3 continues on the frozen stage2 lineage (`s3_fable61` gate PASS).
The workaround-removal PR stays DO NOT MERGE until this is resolved.
