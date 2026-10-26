# Typed-record candidate: bounded qualification result

STATUS: FAIL. Phase 3 and feature completion are unproved; no landing authorized by these results.

Candidate source head: `c7fab8dd802d7428044bd3426bbc9cf26a97e151`.
Producer: `ce8801e1c8ecf20ac794395e007421ceccf6a467dbfc03facd73f0cc3ad06d44`.
Source snapshot: `9baa85ce296addf0a9a970cb8f19912390d0de1dc837d5773c850f6cc2fecb53`.

The fresh Phase 2 compiler build compiled 1400 modules with zero failures
(416.2 seconds compilation, 19.5 seconds link). Both ordinary and bootstrap
frontend sanity modes passed, including positional Hello World. Struct
receiver/runtime capability passed and an immutable runtime capsule was admitted.
These results prove Phase 2 admission only.

The expanded imported-record native probe compiled and ran with exit 0,
printing `IMPORTED_STRUCT_INEQUALITY_NATIVE: PASS`. It checked parameter and
array-element custom equality/inequality, scalar multiplication, and a
record-returning addition with a second preserved field. Peak sampled RSS was
4592200 KiB; the collector proved quiescence. Evidence and input pins reside in
`build/native_probe/imported-inequality-typed-record-<producer>/`.

The store-accounting probe then failed compilation, exit 1: HIR completed
197 modules, but MIR completed 188 and failed 9. Diagnostics reject operator
calls on `lib.scv.distributed_identity.EntityUid` and `SettledAlias`, including
production identity, patch, snapshot and confidentiality consumers. No store
executable or runtime assertion was executed. Raw logs, deduplicated diagnostics
and a hash-bound JSON receipt are retained in
`build/native_probe/store-accounting-typed-record-<producer>/`.

The owned full-CLI qualification run was stopped after this terminal failure;
its caches remain in `bootstrap-items247-typed-record-v2`. It cannot certify
Phase 3. This candidate reaches the bounded compiler-repair cycle limit; no
fourth repair/rebuild is attempted here.

A fresh fetch identifies release_phase3 at
`d9e177de79ac599ecd4b165e39c26d99f037c357`. Since this candidate's
`2f235eccbf4` base, upstream added structural record/enum equality in
`90d1f293648`, further trait-cast fixes, reverted the packed-i64 lane, and
merged PR #4014's full-CLI internal-linker implementation/evidence. The compiler
file overlaps directly. Reconcile these upstream owners before any subsequent
candidate; do not add scalar-wrapper equality boilerplate merely to conceal
an unresolved compiler contract. All selected item 2/4/7 requirements and the
source-matched Stage4/SPipe/manual gates remain retained, not waived.

Nothing was pushed or landed. The successful small native probe is not
whole-compiler, whole-feature, or Phase 3 qualification.
