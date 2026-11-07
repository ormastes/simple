# Pure native composite packed U64 readback exits31

ID: native_composite_packed_u64_readback_exit31_2026_11_07
Severity: P2. Status: fixing, owner `seed_bool_parameter` by explicit agreement; no repair or verification pass claimed.

## Actual observation

The retained pure c56 target executed once in `build/review/pure-c56-target-only3/`. Its stdout contains exactly `BOXED_U32_LAYOUT_READBACK_OK` and `BOXED_U64_LAYOUT_READBACK_OK`; stderr is empty. It then exits31 at a composite OR of four packed-U64 index comparisons. This does **not** establish that all four indices failed or dynamically identify the first failing index/value. `PACKED_U64_FILL_READBACK_OK` and `NONZERO_U8_FILL_READBACK_OK` were not reached: both remain UNRUN, not PASS or independently observed FAIL. No target or prior-green replay was performed for registration.

The fixture constructs packed storage with `rt_array_new_with_cap_u64(4)`, pushes8,0xFF000000,0x8000000000000000 and0xFFFFFFFFFFFFFFFF, then compares the four reads. The explicit U32 accessor comparison after that OR was not reached. Exact literal materialization was independently traced in the retained AOT; this is not evidence of a dynamically observed packed read value.

## Bound producer, source and target

- Pure producer: `build/review/phase2-d128-producer-20261107/construction3/output/simple-bootstrap.exe`, SHA256 `c56bbec927b380e9d50820c7c81ebbaf6de5648c34bf879c895f27fb27df1518`. Its private construction source is `4fa7f05fa5ff55af6ac3199fea563e3800ed8b74`, source-authority SHA256 `51315c947e067a958a21f0fa7f4110acff2ea1d679de859ebe5ab7156dbb3acd`. This provisional producer is not a formal product promotion.
- Actual target source: private commit `e74a1e15f4189c9a653e5f8878d266caaaa119a1`, release parent `bbb25521ae79d928ed6a07c3594327eeb3587f4b` plus explicit fixture carry. Source-authority SHA256 `47432d158e1f0ae75476abb28b6846b02e5719102c623e2eed20c2e5f97cb21c`; authority path `build/review/phase3-c56-latest-source-20261107/source-authority.json.interoperability`.
- Exact authenticated entry: `build/review/phase3-c56-latest-source-20261107/source/test/fixtures/bootstrap/typed_word_layout_readback.spl`; identical retained copy `build/review/pure-c56-target-only3/fixtures/typed_word_layout_readback.spl`, SHA256 `e3dc6ab8e6ee13d71264a3a3bdf4b1ac97f251b4263aac4aac25ce1c03014037`.
- Actual target: `build/review/pure-c56-typed-readback2/attempt1/output/readback.exe`,218624 bytes, SHA256 `cebc8dbea4297b2280ec30df9bef4f6be3204991fc8b62f8fd91d7da51ad9900`. Build transcript `command.transcript` SHA256 `974812a70ba2e913451f0bc8b493542f35ea3d8957cbdc0ce6be47c23a316b35` records x86_64-pc-windows-gnu, LLVM, core-c-bootstrap, entry closure and one-binary mode. The retained target-only campaign did not recompile it.
- Actual target argv is that executable alone, no arguments; working directory `build/review/pure-c56-target-only3/target-run/cwd`. `target-exec.py` strips SIMPLE_/SPIPE_ selectors and uses only Windows/System32 and Windows on PATH. Monitored tree root23504 completed exit31/quiescent1, peak23228KiB. `target-run/exit` is31 and the selected input manifests before/after are byte-identical.

## Actual-image representation diagnosis, not dynamic index proof

The readonly GC provider audit binds the same actual PE before/after. Its packed-U64 constructor sets flag0x10 and allocates8-byte slots. Actual generic `rt_array_push` tests byte flag0x8 only, and its nonbyte path stores the incoming RuntimeValue word unchanged. The canonical checked U64 getter intentionally returns raw slot bits when flag0x10 is set. Actual `rt_value_int_wide` boxes small integers by shifting left3 and uses INT1 boxes for full-width values.

The retained caller AOT shows all four `.push` calls passing through `rt_value_int_wide` then generic `rt_array_push`, with subsequent reads using `rt_typed_words_u64_at`. This source/actual-PE chain supports a producer/provider representation mismatch: RuntimeValue words enter packed raw-word storage. For input8 it statically predicts stored/returned64 rather than8, assuming the successful call path. **That prediction was not dynamically read or localized to the first failing index.** Ordinary boxed arrays correctly take the getter's decode branch, explaining why their controls can pass.

The historical producer owner is `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, `lower_unresolved_array_push`/`box_runtime_value`. Do not globally unbox every U64 push: boxed U64 arrays share the element type. In the actual target source, `rt_array_push_i64_raw` merely aliases generic push and is not a proven representation-normalizing alternative. The active owner is preparing a separately reviewed canonical typed layout dispatcher preserving boxed and packed callers; no candidate is qualified by this record.

## Retained evidence and provenance limits

All paths below are under `build/review/pure-c56-target-only3/`:

| Receipt | SHA256 |
| --- | --- |
| RESULT.sdn | b5c88cb76d66d3e0c3dd148ca6a3a95fe37bf95aa3f33512894e96f73e1cd3d1 |
| target-run/before-selected-inputs.sdn and after-selected-inputs.sdn | f49b0800175fc5dc3ca4a383f3e910862406512f39e104c741c3e2fef3a8ae5a |
| target-run/stdout.bin | 3fa047d0fa8eb8d0c0f5f09f1705a678bffccf85cb0779e79bb6bfe1ef5f9fd2 |
| target-run/stderr.bin (empty) | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| target-run/target.rss.env | af9e365e5610d0e4f4849fb29fe877b0212c27536c7f5c5f080a10976e110005 |
| gc-provider-audit/ACTUAL-PROVIDER-DIAGNOSIS.md | d19aa64987a1ee145f67a514809c3a7b5d7015edf9eb6c8e9286f049e9c6c492 |
| gc-provider-audit/BINDINGS.sdn | fbf7af2f5c9ff08b7afe2295b4205f2c7cf7c1f94b7c06e979373aa3d7a1ab6a |
| gc-provider-audit/ACTUAL-PE-PROVIDER.asm | 3a1108cf6bf668777ceb966a5e914709ea09e5c8a697781d99e41471d5b73006 |

The actual selected link RSP SHA256 is `906703021e4d273337502faf9ab5807d94fba879cf4b855caebe9c9ae6435e75`. It names direct temporary C objects that were deleted after linking. No target C archive/member digest is invented, and the producer-construction archive is not substituted as target-provider proof. Actual strong PE symbols/Windows-UCRT imports and retained disassembly support the diagnosis; deleted-object qualification remains a gap. Prior Hello300-second performance failure and formal product-promotion block remain retained.

## Duplication and ownership

The duplication audit found no exact duplicate; current canonical records were rechecked before insertion. Related records remain distinct and unchanged: `generic_struct_field_untagged_payload_seed_2026-08-21` is a historical generic scalar return; `result_struct_payload_pushed_into_struct_array_crashes_2026-10-25` is a struct-pointer/Result push crash; `sosix_stage2_blocked_by_runtime_wide_int_merge_2026-08-11` is runtime integration; `stage2_if_val_struct_option_binding_as_int_wide_2026-11-03` is an Option binder. Their observations/claims are not merged. Landed getter/index/loop repairs #7697/#7703/#7707 repair read paths and do not supersede this actual packed push observation.

`seed_bool_parameter` explicitly agreed to active fixing ownership for this new ID. Registration adds only the observed P2 record, description, agreed fixing claim and this report. No new tests/builds, no closed/verified state, no workaround fixture edits and no campaign reset. Preserve two boxed greens, the composite failure and both unreached criteria exactly; future changed-source qualification requires root admission and must not replay unchanged passing criteria.
