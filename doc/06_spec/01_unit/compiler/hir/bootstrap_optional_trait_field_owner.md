# Bootstrap optional trait field ownership

Rust source: `src/compiler_rust/compiler/src/hir/lower/tests/trait_field_receiver_tests.rs`.
Native fixture: `test/fixtures/compiler/native_generic_optional_trait_field.spl`.
Executed source: `f38ce63f073bc63e26075e4238aad3d2b8e9ada5`.
Producer SHA-256: `1428b5b7bd447058193626388b5e178dabb2913d059e03fa68b47e99c4bc9d93`.
Status: focused Rust suite **5/5 PASS**; native generic-owner fixture **8 assertions PASS**; production store fixture **16 typed/lifecycle assertions PASS**. Direct chained generic-class result printing remains incorrect and is not claimed passing.

The existing direct-field and field-initialized-local regressions remain. New HIR/MIR scenarios require exact Reader/Other declaration owners and distinct read slots through non-generic if-val, generic field Some/if-val, and generic optional parameters. They reject trait metadata on whole Optional carriers, bare match bindings, unrelated Any fields, and same-field names in different receiver classes. An imported field alias must select the provider's slot despite a colliding trait name in the caller. No concrete implementation is needed for the declared-table lowering assertions.

The native fixture has two real CellOwner<i64> implementations. Both begin with distinct values, support if-val and Some reads, and implement different write behavior. Eight assertions expect initial values 11/29, writes yielding 7/107, and None branches yielding -1/-2. Successful output must be `native_generic_optional_trait_field: 8 checks passed` with exit zero. The production detached-store repro must also link; a standalone fixture alone is insufficient to close that failure.

These are bootstrap producer regressions, not permission to use the seed as normal tooling. Existing ownership/import collision and signature rules must remain intact. Execution receipts must name exact producer/source identity and distinguish diagnostic compilation from admitted Stage 3 native qualification.

Evidence root: `/Users/ormastes/simple-phase3-recovery-16e6180752d/.simple/storage/build/bootstrap/patched-owner-dispatch`. The Rust log is `rust-unit-f38ce63-20261114.log`; native logs are `native-one-run.log` and `diff-production-store-assertions-run.log`. The latter retains both the incorrect direct print lines and the final typed/lifecycle pass marker. No assertions or production source were weakened after execution. These checks are targeted bootstrap diagnostics, not Stage 3 qualification.

Expected direct production-store printing remains **FAIL / UNRESOLVED**, recorded in `doc/08_tracking/bug/attribute_store_chained_result_print_unresolved_2026-11-14.md`. Both old/new simple generic-class and free-function probes printed normally, so they do not establish a regression classification. Full Stage 2 rebuild was not rerun.
