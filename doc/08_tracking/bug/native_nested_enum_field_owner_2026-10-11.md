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
