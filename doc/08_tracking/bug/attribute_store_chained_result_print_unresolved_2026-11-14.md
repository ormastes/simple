# AttributeStoreV1 chained result printing remains incorrect

Status: **UNRESOLVED**. The expected-output check fails. This record does not establish whether the behavior predates the optional-owner repair or is a regression from it.

Observed repaired source: `f38ce63f073bc63e26075e4238aad3d2b8e9ada5`; Rust Cargo producer SHA-256 `1428b5b7bd447058193626388b5e178dabb2913d059e03fa68b47e99c4bc9d93`. Reference old producer: `1bde7c11e1448e2d244a590b83adf68989ee3520fe36b8bc5cf2142532f2f13f`.

Evidence root: `/Users/ormastes/simple-phase3-recovery-16e6180752d/.simple/storage/build/bootstrap/patched-owner-dispatch`.
Concrete reproducer: `differential/production_store_assertions.spl`, SHA-256 `303e358703eafb85bcd7a4ca9fea5dbf19ba520c56cc3df2e8f940c39f4a844e`. It creates two real AttrOwnerV1<i64> implementations and one detached Column store, sets values 11/22/33, and prints each chained `store.get(index).unwrap()` result. Build log: `diff-production-store-assertions-f38ce63.log`; run log: `diff-production-store-assertions-run.log`.

Expected numeric output: 11, 22, 33. Actual lines: `true`, `<value:0x16>`, `<value:0x21>`. The executable exits zero after its 16 separate typed-value and lifecycle assertions and the marker `production-store-typed-lifecycle-checks-passed`. Those assertions confirm typed retrieval, has/retire/absent behavior on this fixture; they do not make the direct printed output correct.

Bounded old/new differential probes using a free generic Result function and a small generic ResultBox<T>.get() class both print 11/22/33 normally. They do not reproduce this production-store failure and cannot classify it as pre-existing or newly introduced. The original production store did not link under the old producer, preventing a direct old/new output comparison on that exact fixture.

The optional-owner repair's linked calls and typed/lifecycle behavior have separate passing evidence. Full expected-output equivalence remains failing here; no no-op owner, source workaround, weakened assertion or fix is claimed. Full Stage 2 rebuild and Stage 3 qualification were not rerun for this report.
