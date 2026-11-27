# stage2_emit_archive_argv_overflow_win_2026-11-02

- Status: **fixed in source by PR #5805** (`emit-archive` passes objects to llvm-ar via an `@response` file);
  the frozen stage2 (ef0681fc0e1) is still affected, so the phase-3 manual flow keeps WA-AR-1.
- Severity: P1 on Windows (no stage3 archive)
- Workaround: WA-AR-1 (`doc/03_plan/bootstrap/workaround_inventory_2026-11-01.md`)

## Symptom
Phase-3 run r11 exited with rc=1 and no archive. `build.log.err` line 7357462 has:
`error: emit-archive failed: process spawn failed: C:\msys64\clang64\bin\llvm-ar.exe: (os error 206)`
(ERROR_FILENAME_EXCED_RANGE). The "[NATIVE] compiling 0 modules" line just before it is benign: the 32 MIR
shards had already emitted all 1414 objects.

## Root cause
`src/compiler/80.driver/driver_aot_native_output.spl` (ef0681fc0e1:3226, df3a14d194b:3227) put every
object path on the llvm-ar argv. 1414 paths come to about 121.6 KB, which is over the 32767-char
CreateProcess limit.

## Workaround (manual, no source change)
`llvm-ar rcsD stage3_closure.a @ar.rsp`, with one quoted path per line. Probe: rc=0, 59,184,150 bytes,
1414 members.

## Fix
PR #5805: `src/compiler/70.backend/linker/archive_response_file.spl`, wired into
`driver_aot_native_output.spl`. Spec: `test/01_unit/compiler/linker/archive_response_file_spec.spl`.

## Removal condition
Stage2 has been rebuilt from a tip that contains #5805, and `--emit-archive` succeeds on Windows with the full
stage3 object set.
