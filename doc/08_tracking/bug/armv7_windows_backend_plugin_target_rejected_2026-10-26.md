# armv7-w64-mingw32: backend plugin load rejected (2026-10-26)

**Date:** 2026-10-26
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs/`, `C:/dev/hircfg-probe/summary.txt`
**Compiler:** `build/s2hw/stage2.exe`, run as `native-build --source src --entry src/hello.spl --target <triple> --cache-dir C:/dev/hircfg-probe/cache --emit-object`
**Severity:** P2

## Symptom

`armv7-w64-mingw32 rc=1 t=6.6` in `summary.txt` (every other probed target is rc=0).
`logs/armv7-w64-mingw32.log`:

```
[ERROR] BACKEND_SESSION_AUTHORITY: load rejected: BACKEND_PLUGIN_TARGET: armv7-w64-mingw32
[first-compile-error] BACKEND_SESSION_AUTHORITY: load rejected: BACKEND_PLUGIN_TARGET: armv7-w64-mingw32
[ERROR] MIR shard error: BACKEND_SESSION_AUTHORITY: load rejected: BACKEND_PLUGIN_TARGET: armv7-w64-mingw32
```

Frontend and HIR phases complete; the failure is at backend session admission.

## Suspected area

`src/compiler/00.common/backend_plugin/receipt.spl` (BACKEND_PLUGIN_TARGET
check): the armv7 Windows triple is not in the accepted target set of the
backend plugin, while i686 and aarch64 mingw triples are.
