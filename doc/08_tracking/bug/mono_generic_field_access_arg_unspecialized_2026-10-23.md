# Stage 2 mono leaves `transient_promote<T>` unspecialized for field-access args

Status: OPEN (workaround in place)

Symptom: a Stage 2 producer native-building `src/app/cli/bootstrap_main.spl`
(Phase 3) fails after HIR (1471/1471 ok) with
`error[E-MONO-033]: monomorphization left 4 generic call site(s) unspecialized`
and `E-MONO-032: call to generic transient_promote at
src/compiler/00.common/cache/reverse_reference_facts.spl:144..147`.

Cause (observed): the calls added in ff1f69fd931 pass a class field access
(`batch.facts`, `batch.known_families`, ...) as the generic argument. Mono does
not infer `T` from the field-access argument type. The neighbouring call with a
plain global (`transient_promote(_reverse_reference_module_batch_v1)`) is
specialized.

Workaround: bind each limb to an annotated local, promote the local, and mirror
the same handle into the globals (tagged `@workaround` in
reverse_reference_facts.spl). Removal check: rebuild Phase 3 with the original
`transient_promote(batch.facts)` form once mono infers T from field access.

Producer: Stage 2 sha e087ff56ba69c386 (cranelift, aarch64-unknown-linux-gnu).
