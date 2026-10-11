# BUG-IT-3 — stage2 native path: generic `impl<T>` method call links against a symbol nothing emits

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. Stage2 under test:
`C:/dev/simple-bootstrap-storage/ladder-s3/s2/simple.exe` (sha256 49cbd00527...), release/1.0 @ b68c0c65708.

Repro (end-to-end): `test/fixtures/bootstrap/stage2_micro/micro_e/main.spl` —
`struct Box<T>: item: T`, `impl<T> Box<T>: fn get(self) -> T`, `Box<i64>(item: 7).get()`.
Run: `STAGE2=... RUNTIME=... sh test/fixtures/bootstrap/stage2_micro/run.shs micro_e`.

Symptom: parse/HIR/MIR/codegen all report clean; `[mono] generic_fns=1 call_sites=2
specializations=2 unresolved=0` in the first sighting (micro_b: counts only the free generic
`pick_second`; the generic impl method is not counted at all); then
`lld-link: error: undefined symbol: ...Box.get` -> `LLVM native linking failed` (rc=1, ~110-200 s).

Why it matters: `generic_class_impl_template_lowering_spec` pins that a generic impl method is a
"non-emittable template", but nothing pins its CALL SITE on the native path: it is neither
specialized nor diagnosed, so the failure surfaces as a linker error with no source location.

Ask: specialize `Box$i64.get` and repoint the call (40.mono today rewrites only free generic
fns), or fail closed in 40.mono/80.driver with an `E-MONO-*` naming the call site before link.
