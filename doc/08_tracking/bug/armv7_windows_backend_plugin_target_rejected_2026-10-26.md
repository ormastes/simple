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

`src/compiler/70.backend/backend_plugin/builtin_adapter.spl` (`builtin_backend_target`, line 130, accepts `arm` but not `armv7`; `supports_target` check at line 193; BACKEND_PLUGIN_TARGET
check): the armv7 Windows triple is not in the accepted target set of the
backend plugin, while i686 and aarch64 mingw triples are.

## 2026-11-03 source candidate: repair the request projection owner

Claim: `p2-armv7-windows-20261103` (broker admitted at 08:31:00Z).
Latest release still omitted `armv7` from `driver_backend_plugin_target` in
`src/compiler/80.driver/driver_backend_plugin_selection.spl`. The driver
therefore passed `armv7-w64-mingw32` verbatim to descriptor admission, whose
supported targets are architecture selectors. Admission rejected the request
before `builtin_backend_target` could run. The adapter and LLVM descriptor
already support canonical `arm`; LLVM's explicit-target owner also recognizes
`armv7`. Adding full triples to the adapter alone would not repair this first
failing boundary.

The candidate maps the `armv7` architecture to existing canonical `arm` alongside
the existing Thumb aliases. It does not broaden descriptor capabilities,
substitute providers, or change the LLVM target-triple/ABI configuration owner.
Four authored scenarios in the existing driver selection spec cover the exact
Windows request and a retained LLVM session, adjacent ARM target environments
and existing aliases, an unknown architecture rejection, and Cranelift's
continued rejection of unsupported ARM.

**TEST_BLOCKED:** no admitted pure-Simple self-hosted CLI is available. These
scenarios and the required compiler/lib/MCP/LSP checks and native runtime smoke
remain unexecuted. No behavioral PASS or actual positive test count is claimed.
Native object architecture/format, Windows ABI and final linking are separate
required qualification gates; projection/admission assertions do not prove
emission or linking. Keep the candidate draft and this bug open pending those
gates and final review.
