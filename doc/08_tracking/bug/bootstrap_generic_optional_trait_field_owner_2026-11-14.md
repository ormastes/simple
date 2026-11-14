# Bootstrap generic optional trait field loses declaration owner

Producer/source evidence: revision `16e6180752d3e75cacb335641451cc6d44607667`; Rust Cargo producer SHA-256 `1bde7c11e1448e2d244a590b83adf68989ee3520fe36b8bc5cf2142532f2f13f`. Parent confirmed identical bytes in Cargo bootstrap output and the stage2-runtime-authority executable; the directory name alone is not provenance.

Retained evidence: `/Users/ormastes/simple-phase3-recovery-16e6180752d/.simple/storage/build/bootstrap/owner-dispatch-repro/evidence.sdn` and `attempt1.log`. Importing/reaching the production detached AttributeStoreV1 produces undefined owner_read/owner_write references from has/get/set/retire. An unused generic template fixture links and runs. The evidence records an accidentally duplicated external runtime-path prefix, so it is diagnostic-only and does not validate runtime-path admission or Stage 2/3.

Source gaps in the Rust bootstrap producer: declared_trait_dispatch only recognized Simple types; field metadata discarded Generic/Optional AST structure; optional subject propagation recognized identifiers only. Losing declared payload identity permits MIR's impl-less trait fallback to emit bare static calls. This is a generic compiler ownership issue, not an ARM backend diagnosis.

Repair retains one authored field-type registry keyed by receiver TypeId with declaration provenance. Conflicting owners sharing an ID are tombstoned rather than guessed. Direct fields can resolve Simple/Generic traits; Optional fields only transfer the inner identity to payload bindings. Provider field aliases resolve in the declaring owner's trait/import table, never the caller's same-spelled trait. Existing Some/if-val binding behavior and Option carrier semantics remain intact. No dummy owner, dead-arm deletion, or method-name inference is introduced.

Related reports remain intact: native_trait_optional_payload_identity_2026-10-08 (pure-Simple optional payload metadata) and native_codegen_trait_field_receiver_erased_ambiguous_2026_10_26 (Rust direct trait fields). This extends the generic optional-field case; it does not claim their whole scope complete.

Executed repair source: `f38ce63f073bc63e26075e4238aad3d2b8e9ada5`. Patched Cargo producer SHA-256: `1428b5b7bd447058193626388b5e178dabb2913d059e03fa68b47e99c4bc9d93`, retained at `patched-owner-dispatch/candidate-f38ce63/simple` under the recovery evidence root above. This documentation update does not change the tested production code.

Observed results:

- Focused Rust HIR/MIR suite: 5 passed, 0 failed (`rust-unit-f38ce63-20261114.log`), including provider alias/caller collision and Optional-carrier negatives.
- Native generic optional-field fixture: linked, ran with exit zero and `native_generic_optional_trait_field: 8 checks passed` (`native-one-f38ce63-20261114.log`, `native-one-run.log`).
- Production AttributeStoreV1 two-owner plus detached fixture: linked successfully. A follow-up retained fixture passed all 16 typed-value/lifecycle assertions and emitted `production-store-typed-lifecycle-checks-passed` (`diff-production-store-assertions-f38ce63.log`, `diff-production-store-assertions-run.log`).
- Direct printing of chained generic class getter results still rendered `true`, `<value:0x16>`, `<value:0x21>` instead of 11/22/33 despite typed assertions passing. This result is not a full output-equivalence pass; the separate unresolved report is [attribute_store_chained_result_print_unresolved_2026-11-14.md](attribute_store_chained_result_print_unresolved_2026-11-14.md). Old/new free-generic and small generic-class probes both print normally, so neither pre-existing nor regression classification is established.

All current logs are under `.simple/storage/build/bootstrap/patched-owner-dispatch` in the recovery checkout. These targeted results do not admit Stage 2/3, qualify Hello/link parity, or close unrelated generic printing behavior.

Full Stage 2 rebuild was not rerun. The review/landing scope is the demonstrated owner-identity/link repair, not a claim that every production-store output or bootstrap gate passes.
