# MIR declaration projection depends on native dictionary allocation order

Status: repair prepared; admitted native regression and production-route verification pending.

The admitted Phase2 producer `e0967dd29d57d9a007d5515a94cfd1a7fff9229c4e9ffd2b80a254627b1857f1` reached MIR after 21 HIR modules and final archive publication for VMM. The retained log `/tmp/simple-phase2-attempt8-vmm-integrity-cwdfix-20261030/attempt/vmm/build.log` reports `borrowed MIR declaration records differ from selected complete body` beginning at line 1739. Frozen producer source `/tmp/simple-phase2-runner-attempt8-20261030` is unchanged.

## Contract defect

`hir_declaration_summary_v1.spl` projected seven SymbolId-keyed dictionaries through `values()`: functions, structs, classes, enums, traits, bitfields and constants. `hir_declaration_codec_v1.spl` hashes the resulting arrays in their stored order. Meanwhile `generated/hir_codec.spl` serializes these dictionaries in canonical numeric SymbolId order. Thus equal complete-body bytes need not produce equal declaration digests.

The native runtime's `rt_dict_values` walks occupied hash slots (`runtime_native.c:11621`). Struct keys hash by their boxed word/address (`rt_core_dict_hash`), and `hir_codec_key_order.spl` explicitly documents identity-keyed SymbolId dictionaries. Independent body decodes allocate different keys, permitting different projection array orders. This is a concrete nondeterminism defect and fits the observed boundary; the failed run did not retain per-row digests, so the precise first differing row remains unobserved.

## Repair and regression

Use the complete codec's existing `hc_order_symbol_id_keys_v1` helper for all seven dictionary projections, retaining original key objects during lookup. Preserve ordered fields, enum variants, trait methods/defaults and implementation arrays. Keep every complete-body, declaration and authority integrity check intact.

`test/fixtures/compiler/mir_declaration_canonical_order_repro.spl` is a native fail-fast mechanics fixture with multiple declarations of each kind. It requires increasing symbol order, identical projection digests across three independent complete-body decodes, and a changed-header negative control. It grants no final archive admission. The prior one-function borrowed-module fixture cannot expose unordered multi-row projection.

Validation completed: whitespace/diff check. Remaining: compile and execute the fixture with the admitted pure compiler, obtain independent review, integrate into an isolated producer candidate, then rerun the focused VMM production route through the build owner. Do not invalidate or delete prior admitted caches to hide this failure; regenerated declarations require the fixed producer identity.
