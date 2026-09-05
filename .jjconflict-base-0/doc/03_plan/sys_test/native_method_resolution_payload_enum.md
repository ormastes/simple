# Native method-resolution payload enum — system test plan

## Scope

The unit, integration, and system scenarios cover the five
`MethodResolution`-shaped enum variants, static type-owner factory recovery,
inferred empty-array `push`, and inferred scalar/folded-binary module constants.
It rejects the Rust seed, stub fallback,
missing binaries, compilation failure, execution failure, and missing verdicts.

Interpreter-only enum behavior and source-text assertions are controls, not
acceptance evidence. Stage3/Stage4 admission remains a separate bootstrap gate.

## Environment and execution

Run with an admitted pure-Simple full CLI at `bin/simple`:

```sh
bin/simple test \
  test/01_unit/compiler/driver/method_resolution_match_classification_spec.spl \
  --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test \
  test/02_integration/compiler/native_method_resolution_payload_enum_spec.spl \
  --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test \
  test/03_system/compiler/native_method_resolution_payload_enum_spec.spl \
  --mode=interpreter
```

The SSpec invokes
`scripts/check/check-native-method-resolution-payload-enum.shs` once and shares
its fail-closed result across all scenarios. Evidence is retained below
`build/test-artifacts/native_method_resolution_payload_enum/`.

## Traceability

| Requirement | Scenario coverage | Executable spec | Manual |
|---|---|---|---|
| REQ-BST-ENUM-001 | unit payload matrices; native compile/run integration; static factory; inferred push; inferred module constants; unavailable/error path | `test/01_unit/compiler/driver/method_resolution_match_classification_spec.spl`; `test/01_unit/compiler/mir/folded_const_type_classification_spec.spl`; `test/02_integration/compiler/native_method_resolution_payload_enum_spec.spl`; `test/03_system/compiler/native_method_resolution_payload_enum_spec.spl` | `doc/06_spec/03_system/compiler/native_method_resolution_payload_enum_spec.md` |

PASS requires five executed examples, an explicit native probe PASS, zero
stubs, a current generated manual, and no executable specs under `doc/06_spec`.
