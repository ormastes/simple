# XRay Windows flag-guard: `dllexport` globals disable MinGW auto-export (2026-11-15)

Status: verification-pending (lane xrayring, `work/xray-win-ring-20261115`)

## Symptom
An `--xray --backend=llvm` Windows DLL of `test/fixtures/xray/xray_inprocess_prog.spl`
exported only the four xray symbols and **no function**:

```
off DLL (xray off):  add1, scaled, traced   (module-qualified names)
on  DLL (PR #9281):  __simple_xray_descriptor_v1, __simple_xray_hook_v1,
                     __simple_xray_names_v1, __simple_xray_ring_v1
```
(`llvm-objdump -p`, llvm-mingw 20260922 UCRT, seed-attr.)

## Cause
lld in MinGW mode auto-exports every external symbol **only when no object carries an
explicit `dllexport`**. PR #9281 emitted `dllexport` on the descriptor, names and hook
globals, so auto-export switched off and the host could resolve no function to call. The
earlier 128 s probe (lane xrayfg) built with `XR_XRAY=0`, so no `--xray` DLL had been
checked for function exports before this lane.

## Fix
The xray globals are plain external `global`/`constant` (no `dllexport`) and reach the
export table through the same auto-export as the functions
(`_MirToLlvm/core_codegen.spl emit_xray_flag_guard_globals`). Off identity is untouched
(an off module emits no xray text).

Repro + generalisation: `test/01_unit/compiler/backend/xray_llvm_attrs_spec.spl`
("emits no dllexport in a windows xray module (repro)", "... with several sled and
never-listed functions"); RED 21/27 before, GREEN 27/27 after.

## Open
The MSVC lane (lld-link) has no auto-export at all, so neither functions nor xray
symbols are exported there; it needs an explicit export list (owner decision).
