# Folded enum discriminants through the real compiler consumer

Requirement: REQ-MC-003. Executable spec: `test/02_integration/compiler/enum_discriminant_adapter_spec.spl`.

Status: authored review manual; execution and SPipe generation **UNRUN**. The observations below are assertion oracles, not recorded results.

1. Parse and lower each source fixture. Require the expected enum and variant counts, no HIR lowering errors, preserved explicit flags, and the expected expression kind before inspecting diagnostics.
2. For `A = 2 + 3; B; C = 6`, require `E-CLOSED-002` identifying `B / C = 6`. A collision-free `A = 1 + 4; B = 0` must remain silent. Nested multiplication and all ten supported integer binary operators must retain their exact values. Nested Neg/BitNot must remain supported.
3. For evolving u8 declarations, folded256 and folded-1 must retain the existing `E-EVOLVING-002` representability diagnostic; they are successful integer folds, not constant failures.
4. For division/modulo by zero, module-constant references and calls, retain the explicit Unavailable failure. For bool, float, plain string and negated float, retain NonInteger. Require the enum name, variant name, original span, unchanged fatal message and failure count.
5. Inspect the additive declaration report and full module report. A failed enum must not produce fabricated duplicate diagnostics, and every explicit failure must survive both reports.
6. Inspect the actual `collect_module_enum_contract_receipt_v1` under Moderate, Strict, Robust and Critical. Constant failures are errors under every profile. Existing contract diagnostics preserve their earlier warning/error treatment.
7. In one mixed module, retain the independent malformed-condition diagnostic, the successful neighboring enum's collision, and a third enum's explicit failure. The critical receipt must retain all three findings.
8. Inspect compatibility collectors: legacy diagnostic-array APIs may be empty for a constant failure; the richer report and actual consumer must retain the failure. These collectors are not admission receipts.

The unused internal compiler helper exports `variant_shape` and `enum_variant_shapes` are retired with explicit root authorization after a bounded outside-caller check. Private structured Result adapters replace them. Public diagnostic-array and module-report entrypoint signatures remain intact; the full module report adds `constant_failures`.

The exact reviewed condition baseline and three declaration repair pins are dependencies. This spec does not prove decoding/encoding, native runtime behavior, arithmetic-overflow policy, shift-boundary policy or full REQ-MC-003 completion.
