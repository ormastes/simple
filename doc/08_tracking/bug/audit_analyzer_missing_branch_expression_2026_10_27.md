# Audit analyzer single-call branch expression missing

**Date:** 2026-10-27
**Status:** Parser repair validated; HIR passed; object compile NOT PASS; runtime unqualified
**DB registration:** PENDING

## Failure evidence

The pinned all-objects Phase2 baseline recorded the same parser failure for
both analyzer files:

- `D:\dev\simple-all-objects-phase2-20261027\build\object-campaign\objects\c718ec0c9fbc4f25bdfe45181b7c4bc9\13eb9d0e94faeefa17c850290863fca66c2c43732474614f1beb07e3fff9a93f\compiler.log`
  - `src/app/audit/ffi_analyzer.spl` line 213:17: `expected Indent, got else 'else'`
- `D:\dev\simple-all-objects-phase2-20261027\build\object-campaign\objects\c718ec0c9fbc4f25bdfe45181b7c4bc9\7a88e6bbbfaa8e51deb6baa7123e0fe4fda85c20717909ccd22403b92680a563\compiler.log`
  - `src/app/audit/sffi_analyzer.spl` line 213:17: `expected Indent, got else 'else'`

In each source file, `val todo_comment = if rt_calls.len() == 1:` had no
indented value before its `else` branch.

## Repair

The missing single-call expressions have been restored, preserving each
existing multi-call `else` branch:

```simple
"{spaces}# TODO: Replace direct FFI call {rt_calls[0]} with wrapper {wrapper_names[0]} from app.io or compiler.ffi"
"{spaces}# TODO: Replace direct SFFI call {rt_calls[0]} with wrapper {wrapper_names[0]} from app.io or compiler.sffi"
```

These exact expressions were previously introduced by commit
`e01ae78e5ea65ebbb4a98416c86db2b73d2c94a2` (`fix(audit): restore single-call
wrapper diagnostics`). The current repair is a source syntax correction, not
a producer grammar workaround, so no workaround tag applies.

## Validation status

The changed-input FFI object compile log is
`D:\dev\simple-object-repairs-luna-20261027\build\object-repair\audit-ffi-object\compiler.log`.
The repaired source parses: the log records `phase=parse` complete with 104/104
modules succeeded and zero failed. Root reports HIR passed for all 104 modules.
The object compile is **NOT PASS**: MIR lowering exits 1 with two
`TextIoError.Codec` payload type mismatches and one unresolved `to_text`
method call. No runtime validation has passed or been claimed. The existing
generic audit spec does not exercise these analyzers.

Local read-only tracing found multiple `to_text()` call sites in the 104-file
source closure, including `src/lib/nogc_sync_mut/io/process_ops.spl:2319`
(`pid.to_text()`) and numeric conversions in the common SDN modules. The MIR
diagnostic has no source span, so the unresolved call cannot be attributed to
one site from this log; no follow-up edit is proposed from this evidence.

Canonical bug database registration is pending because the writer is currently
blocked. No database record has been changed by this report.
