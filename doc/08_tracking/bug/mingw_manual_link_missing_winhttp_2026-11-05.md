# Generated MinGW link line / rsp missing -lwinhttp

- **Status:** FIXED (repo script) + drift guard, PR work/mirp2-I. P2.
- **Found:** s3_fable43 relinks (family I3).

## Root cause
The WinHTTP provider (e65e0e6b891, 2026-11-03) added `winhttp` to the driver's
`mingw_libs` in `src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl`
(both lists) and `native_all_support.spl`. Two hand-copied link lines did not follow:

1. `scripts/bootstrap/p3-manual-link-stage3.shs:168` -- writes the clang line and
   `<exe>.link-command.txt` that later relinks copy. **Fixed** (adds `-lwinhttp`).
2. Out-of-repo `C:/dev/p3new/s3new/fable_link.ps1` (copied from
   `linkdry/s3.exe.link-command.txt`, i.e. from #1) -- not in the repo; operators
   must add `-lwinhttp` there (or pass `-Extra @('-lwinhttp')`).

The `*.link.rsp` that s3_fable43 itself writes for user programs lacks winhttp
because s3_fable43 is linked from objects predating e65e0e6b891; current source
emits it. A rebuilt driver object fixes that without further source change.

## Prevention
`test/01_unit/compiler/70.backend/linker/mingw_system_libs_parity_spec.spl`
parses the driver `mingw_libs` list and fails when the manual Stage 3 line drops
any of them (RED before the script fix), plus native-all and second-list checks.
