# C4 checked dictionary Struct projection

Focused native ASan/UBSan evidence exists for the reviewed implementation.
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

Native controls cover raw/tag1 preservation, corrupted projected
foreign/preexisting/wrong-tag values, extent/generation mismatch, one-unit-short
fuel and unchanged epoch, alongside existing alias-Stale/missing/retirement
controls. The Simple fixture is authored UNRUN; it describes real shared-account
tagged output without claiming compiler nominal or lifetime authority.

## Focused native evidence

Attempt1 at source `1b462f50776` failed C compilation because repeated fixture
sections redeclared locals in the same lexical scope. No binary was produced and
no assertions executed. Evidence: `/tmp/read16-native-evidence-20261025/stdout.log`.

Attempt2 at exact source `300f65ab50de24dc203f9fd4822d9f7c6a391d03` changed only
six lexical-scope braces in the fixture. The ASan/UBSan fixture exited 0 with no
findings; address reuse was **not observed**. Binary SHA256:
`c673e84e1e9540e92d7ce31fb6a8d93d5322d5ecde81dea04b8b9a73ac7f5518`.
Evidence: `/tmp/read16-native-evidence-20261025-attempt2/` (source revision,
source hashes, stdout, binary and RSS receipt). Peak sampled RSS was 233836KiB
under a 2GiB sampled guard; receipt `hard_memory_limit=0` means this was not a
hard kernel memory limit. No passing fixture was rerun.

Simple specs and full HIR/SOURCE execution remain UNRUN. This focused native
result does not admit nominal compiler authority, affine lifetime/epoch proof,
private backend publication, final artifact linking, or full SOURCE execution.
