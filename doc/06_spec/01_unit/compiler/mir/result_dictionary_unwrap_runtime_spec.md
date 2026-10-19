# Result dictionary values and module-index consumer

Authored manual for
`test/01_unit/compiler/mir/result_dictionary_unwrap_runtime_spec.spl`.
REQ-ENUM-RESULT-DICT. Six scenarios authored; execution UNRUN.

1. Call a mutable producer once, unwrap its dictionary, and require one call,
   two keys, and exact integer values 17/29.
2. Unwrap an Err dictionary through unwrap_err and require its exact value 43.
3. Read floating 2.5 and text payloads without integer erasure.
4. Unwrap a present empty dictionary and require zero entries and no missing key.
5. Read both fields of a nominal record dictionary value, including distinct
   second-field value 31 to catch wrong-field/owner projection.
6. Invoke the actual ModuleSurfaceBuilder name-index API. Initial and repeated
   identical registration succeed, one name/index row remains, and conflicting
   index 8 returns the exact diagnostic while retaining prior value 7.

Use the admitted existing SSpec native route described in
`doc/07_guide/infra/testing/native_test_binary_workflow.md`. No new runner is
introduced. These are intended executable value oracles, not completed runtime
evidence. Expected process-abort paths are inspected in the companion MIR spec.
