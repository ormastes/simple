# C4 checked dictionary Struct projection

Source-only implementation; executable controls authored UNRUN during Phase3.
This change supplies physical validation, not compiler nominal/lifetime admission.

Native operation16 retains its existing signature, missing=0, positive stored
bits, negative error and unchanged region epoch. SOURCE Struct storage is the
allocation data itself: one eight-byte word per field, without a header.
LLVM ordinary Struct values use raw data pointers; Cranelift ordinary Struct
values use those pointers with tag1. Shape4 value rows declare physical1/raw or
physical2/tag1. This provider never infers a header offset or relabels a word.

The existing dictionary owner authenticates its owner record, current backing
and allocated capacity before prefix access. Its lock remains held while region
enter16 validates control, generation, active state and expected epoch. After
projection, the new C-owner-only validator runs before either lock is released:
it checks the exact declared raw/tag1 form, looks up the untagged identity in the
actual allocation registry, requires a live noncontrol SOURCE member of the same
control/generation, validates its immutable shape1 birth header, and compares the
authenticated allocated byte extent with descriptor extent. No child data loads,
allocation, callback, account reservation or additional lock occur there.
Member retirement closes its region before registry removal; dictionary
retirement closes it before freeing its backing. Reads cannot refresh epochs.

Operation16 work adds a checked dedicated `8*P+256` allowance to the unchanged
region9 and dictionary work bounds. P is the current successful region-registry
probe watermark. There is exactly one additional registry lookup, at most P
probes, conservatively eight logical slot/load/branch/index operations per probe.
The fixed256 separately covers hash/index setup (32), tag validation (32),
member metadata checks (48), immutable six-word header/extent checks (64), and
bound/state/return checks (80). This is a logical conservative accounting policy,
not a physical CPU/RSS theorem. The owner rechecks the combined current allowance
before the first control lookup; the projection checks it again before the
additional child lookup. Registry growth between observation and entry may
therefore refuse, and cannot cause an unpaid lookup. Fields/bytes remain zero.

Native shape4 contains no nominal type ID. Compiler-sealed typed dictionary
birth/put/read recipes must independently prove the exact Named Struct owner
and resolved layout. The separate private backend dictionary publication uses
the positive validated bits directly: LLVM raw-to-pointer, Cranelift tagged
passthrough. Generic Cast and the fresh-allocation publication OR1 are not this
proof. Caller, affine receipt, private backend emission and final artifact seal
remain separate required owners/gates.

Authored native controls cover raw/tag1 preservation, corrupted projected
foreign/preexisting/wrong-tag values, extent/generation mismatch, one-unit-short
fuel and unchanged epoch, alongside existing alias-Stale/missing/retirement
controls. The Simple fixture exercises real shared-account tagged output without
claiming compiler nominal or lifetime authority. No executable jobs were run.
