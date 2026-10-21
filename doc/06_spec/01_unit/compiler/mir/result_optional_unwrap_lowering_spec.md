# Result Optional MIR payload ownership

Requirement: REQ-ENUM-RESULT-OPTIONAL.
Source: `test/01_unit/compiler/mir/result_optional_unwrap_lowering_spec.spl`.
Five scenarios authored; all **UNRUN**. This is a manually maintained document;
docgen was not executed.

The fixture calls the real `lower_result_unwrap_core` with a prelowered
receiver and a deliberately invalid HIR source expression. Lowering that
expression again would fail, so the success cases also constrain receiver
reuse.

| Scenario | Actual production API and required observation |
|---|---|
| Scalar Optional payloads | i64/bool/f64/text inner types retain an i64 carrier, exact Optional HIR type, Optional/tagged flags and a direct payload-to-result copy |
| Nominal Optional payloads | Real SymbolTable Struct/Class/Enum declarations retain their exact nominal Optional owner |
| Wrong or future Result tags | The gate compares exactly 0 for unwrap or 1 for unwrap_err; the mismatch terminator is Abort with the existing direction-specific panic text, without assigning a successful result |
| Unsupported shapes and defaults | Any/Error, narrow/unsigned integers, f32, unknown nominal owners, nested Optional/Array shapes and default-bearing Optional forms remain fatal before runtime calls |
| Wrong nominal declaration | A Function symbol and nominal generic arguments remain rejected |

Each successful scalar probe must contain only `rt_enum_discriminant`,
`rt_enum_payload`, and failure-path `rt_panic` calls. It must not allocate an
Optional, unwrap the inner value, or reinterpret a bool/float/text payload at
this outer Result boundary. This is an emitted-MIR oracle, not a measured
allocation, runtime behavior, or performance result.

Expected mismatch diagnostics:

- unwrap: ``called `.unwrap()` on an Err Result``
- unwrap_err: ``called `.unwrap_err()` on an Ok Result``

Unsupported Optional forms retain the existing diagnostic formatter:
`unsupported Result unwrap payload type: payload is Optional, not a tuple`
(or `unwrap_err`). No diagnostic or authority fallback is introduced.

Use the existing SSpec runner only after a pure-Simple ordinary test CLI is
qualified. The runtime companion and expected-failure native fixtures remain
separate execution gates. No broad enum completion or historical failure
count is inferred from these cases.
