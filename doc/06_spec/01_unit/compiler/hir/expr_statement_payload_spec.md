# HIR expression statement payload

Executable: `test/01_unit/compiler/hir/expr_statement_payload_spec.spl`.
Shared controls: `expr_statement_payload_fixture.spl`.
Native entry: `expr_statement_payload_native.spl`.
Status: authored; execution pending a rebuilt pure-Simple producer. No test PASS claimed.

The three scenarios call `hir_ast_expr_statement_payload_v1` with actual parser
AST constructors. They verify the string `abc` and all source-position fields,
reject Return and Break variants, and reject nil statement/expression payloads.
The native entry calls these same controls and exits nonzero on any failure.
Its successful output must be exactly `PASS expr-statement-payload` plus newline,
with empty stderr and exit zero.

The unchanged end-to-end admission fixture is
`src/compiler/bootstrap_admission/stage2_mir_retention.spl`: `main` evaluates
`print("abc".len())`. A newly built producer must compile it in normal bootstrap
mode zero with HIR caching enabled; the executable must print `3` and exit zero.
The helper tests alone do not qualify compiler admission or smux.
