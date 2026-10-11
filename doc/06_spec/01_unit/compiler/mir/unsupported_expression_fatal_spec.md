# Unsupported MIR expression fatality

Executable: `test/01_unit/compiler/mir/unsupported_expression_fatal_spec.spl`.

This manual is authored from the three executable scenarios. Execution and
generated-doc evidence are pending a corrected, qualified pure-Simple producer.

| Scenario | Real behavior asserted |
| --- | --- |
| Fatal diagnostic and span | The actual MIR owner emits one fatal diagnostic with the exact code, message and source location, while allocating a matching unit-typed recovery local. |
| Diagnostic draining | Two unsupported expressions retain separate fatal diagnostics and distinct unit-typed recovery locals. |
| Advisory control | The ordinary diagnostic API remains nonfatal. |

The native integration gate must compile the independently reproduced rejected
callback fixture with a corrected producer, require nonzero status and the
`E-MIR-EXPR-Lambda` diagnostic, and confirm no executable was published. The
historical producer emitted an executable that crashed at a zero callback.

Status: **UNRUN**. This safety regression does not satisfy a REQ-TRC acceptance
criterion or imply closure support, complete SSpec support, or release readiness.
