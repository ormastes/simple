# Metadata-only classes incorrectly require native objects

Status: OPEN. The source repair is provisionally reviewed; native qualification
against the changed compiler remains pending. This is not an Item 5 completion
or compiler admission claim.

## Observed failure

Qualified pure-Simple producer 8d2b30f60cddb6763aefc9478127d16a3665154521e1d9380033bb2288b71afe
compiled and executed Hello. Three imported-class fixtures (empty array,
nonempty array, dictionary defaults) completed MIR but each exited 1 during
native compilation: its owner has no functions or static data. No executable
assertions ran. All workers were quiescent; no resource stop occurred.
Evidence: build/review/item5-provider-default-qualification-20261107.

## Repair and safeguards

One canonical parsed classifier recognizes classes that own only field
metadata. It rejects methods, unknown attributes and volatile/fixed-address
fields. Both ordinary and retained-source paths use it. Full HIR lowering and
canonical cache publication remain mandatory. Final native objectless
admission still checks matching source/module/path and empty MIR functions,
statics and constants. Actors, free function bodies and executable impls
remain protected by their existing checks.

Field defaults are relocated metadata evaluated by constructor lowering in
the consumer. A callable class counterexample must retain an owner object.
Four executable fixture pairs are under
test/01_unit/compiler/fixtures/native_metadata_class_defaults; all are
UNEXECUTED against the changed compiler. Source review found no introduced
P0/P1 or path bypassing final-empty-MIR checks.

## Remaining qualification

Rebuild the current compiler, compile and execute its Hello, then run all four
fixture binaries and verify the callable owner has a real object. Add direct
negative admission evidence for runtime data, actor bodies, unsupported
attributes and hardware fields. Runtime/std cold-native emission still counts
every class as data and may conservatively reject this case; that separate
guard is unchanged. Full bootstrap, small default image, provider/aspect
dynload, AVX512 DB/HTTP comparisons, CUDA and ARM/RISC-V qualification remain
open under Item 5.

## Classifier spec (2026-11-07)

`test/01_unit/compiler/driver/native_metadata_only_class_objectless_spec.spl`
pins the parsed classifier: classes with empty-array, nonempty-array,
dictionary or no defaults are objectless candidates; a class with an inline
method (carried by its synthesized impl), an explicit impl, a free function
or a constant beside it is not. 4/4 pass on 204128b335a; with the pre-fix
classifier (204128b335a~1) the admission example fails. Native fixture
execution against a rebuilt compiler is still pending, so status is
fix-implemented-verification-pending, not closed. The older
`native_objectless_proof_spec.spl` fails 15/15 on this base because it
imports `driver_native_module_is_objectless`, which no longer exists.
