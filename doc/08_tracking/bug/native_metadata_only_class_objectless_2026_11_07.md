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
