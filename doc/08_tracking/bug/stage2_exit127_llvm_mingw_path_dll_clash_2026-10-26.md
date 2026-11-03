# stage2.exe exits 127 silently on PATH/libLLVM-23.dll clash (2026-10-26)

**Date:** 2026-10-26
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs/`, `C:/dev/hircfg-probe/summary.txt`
**Compiler:** `build/s2hw/stage2.exe`, run as `native-build --source src --entry src/hello.spl --target <triple> --cache-dir C:/dev/hircfg-probe/cache --emit-object`
**Severity:** P2

## Symptom

`build/s2hw/stage2.exe` exits 127 with no output (Windows status 0xC0000139,
entry point not found) when:

- the llvm-mingw `bin` directory is first on `PATH` (its `libLLVM-23.dll` is
  loaded instead of the one stage2 was built against), or
- `SIMPLE_PROJECT_ROOT` is set.

## Workaround

Put `PATH=/c/msys64/clang64/bin` first.

## Repair

`p3-smoke-stage3.shs` now bundles the admitted LLVM runtime DLL closure beside
each Windows stage candidate before executing it. Its version smoke then
deliberately puts llvm-mingw first on `PATH` and sets `SIMPLE_PROJECT_ROOT`, so
the candidate is tested without relying on the workaround above. The focused
`scripts/bootstrap/tests/stage2-dll-path-independence-test.shs <stage.exe>` checker
reproduces the unbundled loader failure, bundles the candidate, and verifies
that it starts under the same conflicting environment.

## The bug

Not the DLL clash itself but the silent failure: no diagnostic names the
conflicting DLL, the loader error, or the workaround. A launcher/wrapper should
detect the loader failure (or pin its DLL directory) and print a one-line cause.

## Triage 2026-11-03 (boot-script-fixes lane)

Deferred: DLL bundling repair is already in p3-smoke-stage3.shs; the remaining ask (launcher that names the loader failure) needs a Windows stage2 run to verify. Still open.
