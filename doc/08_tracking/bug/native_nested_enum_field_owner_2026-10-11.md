# Nested enum-field method owner correction

Status: **source correction; native verification pending**.

## Observed residual and scope

The final runner built by producer SHA-256 `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`, from source `57d83549f09b374ff9105018896843d4f8ff00e9`, visited 218 HIR/MIR modules and still reported unresolved `name` at `flight_rules.spl:503:12`: `rules[i].category.name()`. The previously reported direct record methods were absent from that diagnostic set. This is not an execution PASS or independent attribution to the earlier index-provenance fix.

This correction starts from `a302b218f5d9e6f278fba9bf333220a7d2644c15`, including release #2866. The frozen runner evidence remains at `/home/yoon/dev/simple-phase4-combined-runner-20261011/build/native_probe/phase4-final-integrated/`. No compiler construction or runner retry was performed for this correction.

## Source-supported mechanism

`FlightRuleV1.category` is a `RuleCategory` enum. `register_composite_field_metadata` previously stored its bare name in `struct_field_type_name`, while retaining its qualified identity separately for HIR rebinding. `remember_field_projection_provenance` copies the bare name into `struct_value_syms`. Unresolved method dispatch then skips canonical enum recovery because that recorded owner is nonempty, and initially searches `RuleCategory::name`; the provider registered `compiler.common.assurance.flight_rules.RuleCategory::name`.

Release #2866 normalizes qualified struct layout keys and method owner keys containing `::`. It does not qualify a bare enum-field name. The remaining consumer symbol-table fallback can rescue some contexts, so this source-supported mismatch is not instrumented proof of the final runner's exact metadata state or sole cause.

## Correction

For a field whose declared symbol kind is Enum, store `mir_class_identity(field_type_symbol)` in the projected field's owner-name metadata. Keep its existing `field_type_ownership_key` unchanged. The existing Class branch and method privacy, ambiguity checks, provider registration, and HIR rebinding remain unchanged. No arbitrary method-name fallback or registry-source workaround is added.

## Authored regression and next native gate

`test/fixtures/compiler/nested_enum_field_owner/main.spl` imports two providers defining different `Category` enums with identical variant names, ordinals, and `name()` methods. Exact expected text and an explicit inequality reject foreign-owner capture. It also checks variable-indexed records, nested arrays of records, and a nested record field. Provider record names deliberately differ to isolate the enum-owner collision from independent same-named struct-layout issues.

The fixture is authored but **not compiled or executed in this lane**. The next authorized changed-source native gate must:

1. Use an integrated pure-Simple producer containing this correction and record its SHA-256 and source revision. Run the three-file fixture with explicit `--source test/fixtures/compiler/nested_enum_field_owner --entry-closure --entry test/fixtures/compiler/nested_enum_field_owner/main.spl`, one worker, a private preserved cache, and no stub fallback. Build and execute the ARM binary; require exit 0 and `NESTED_ENUM_FIELD_OWNER_PASS`.
2. Build that same source closure with LLVM 18, `--backend llvm --target riscv64-unknown-linux-gnu --emit-object`, and a separate private cache. Check ELF `e_machine == 243` (RISC-V), not just build exit status. No cross-target execution is claimed.
3. Run the original `test/fixtures/compiler/flight_rule_indexed_owner.spl` with its real registry dependency and require its existing filtering, gap-predicate, and canonical-output oracles. A full runner retry is not authorized by this document.
4. For independent causality, compare the collision fixture against a producer with the same integrated source except this correction. Preserve failures and distinguish compilation success from execution success.

No native gate, broad compiler/core/MCP check, or release qualification is claimed here. Runtime verification remains pending under the coordinator's construction/iteration cap.

## Changed-producer qualification attempt

Producer `/home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/hir-cache-v7/simple`, verified SHA-256 `19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21`, was built by the coordinator from source `5ecfff3d23a31e2f7a5b3c3d1be752f14c53f7f1`, including this correction and HIR cache v7. The original three-file fixture at commit `3a19f9b833ac1569c33233d1751bca03a31fe1ad` was compiled without edits using explicit source root/entry closure, LLVM 18, one worker, private caches, producer-bound `SIMPLE_HIR_CACHE_DIR`, and a 120-second limit.

**FAIL:** the ARM build visited all three MIR modules, then exited 1 with seven unresolved `name` diagnostics at `main.spl:8:8`, `9:8`, `12:8`, `12:35`, `14:8`, `15:8`, and `17:8`. The nested-envelope call at line 19 was not in the reported diagnostic set; absence of a diagnostic is not an execution PASS. No executable was produced and no ARM oracle ran. The qualification therefore does not establish the correction as sufficient for indexed imported enum methods.

The coordinator required stopping at the first semantic failure. The explicit-root RISC-V command was prepared but **not executed**. No RISC-V object/EM243 qualification, fixture workaround, compiler construction, or unchanged retry occurred. Exact commands, log, fixture hashes, producer/source identities, and receipt are under `build/native_probe/enum-field-owner/v7/`; private frontend/native caches are preserved. The independent-causality and native gates above remain unfulfilled.

## Second correction: indexed Struct layout provenance

The hypothesis that a *qualified* enum owner in `struct_value_syms` inherently suppresses correct dispatch was rejected by source analysis: both `mir_class_identity` and `register_provider_method` use the same owner normalizer, and `struct_owner_method_key` accepts a direct canonical row before attempting layout-key conversion. The preserved 19f build log contains no owner/field tracing, so it does not reveal the exact dynamic registry and receiver values. No unchanged fixture build or compiler construction was performed to obtain them.

A narrower missing connection is demonstrable in the nested-array path. Array-return prescan in `module_lowering.spl` only records a named element shape for Class/Struct elements. For `left_grid() -> [[LeftRecord]]`, the outer element is Array, so its shape is `__no_struct_element__`; `remember_direct_array_return_element` deliberately publishes no element-owner note. The two indexes retain `[LeftRecord]` and then `Named(LeftRecord)` HIR provenance via the earlier cd7 helper, but `resolve_base_struct_name` and `resolve_field_index` do not consult the indexed local's HIR note. Direct record-method recovery does consult that note. Field projection therefore has no equivalent path from this declared Struct owner to layout metadata.

The second correction extends `remember_array_index_projection_provenance` to record a proven Named Struct's declared qualified layout key when that layout is registered. It uses `composite_layout_key` and `declared_struct_layout_key`; it does not search by method basename, change provider visibility, mark a scalar as an array, or alter primitive decoding. Enum/Class handling and array storage marking remain unchanged. This supplies the field-layout connection for the nested-array case; it is **not a claim that the other six diagnostics are fixed**.

`test/fixtures/compiler/nested_enum_field_owner/indexed_layout.spl` adds an independent regression with `[[LayoutRow]]`, a typed nested-array parameter, two enum values, and an integer marker before the enum field. Exact marker/name assertions reject field-index-zero fallback. The original three failed fixture files remain byte-identical to the hashes in the 19f receipt, retaining the foreign same-basename owner collision test. Both fixtures are pending one coordinated changed-source native gate; no new native result is claimed.
