# Indirect call helper refers to caller-local bindings

Canonical ID: `indirect_call_helper_out_of_scope_bindings_2026_10_16`.
Bug database reconciliation: pending; no qualified database tool is available.
Status: source repair prepared; runtime and object qualification pending.

Phase 3 cycle 2, source revision `1e93dca4ce3d7be2187da1b67cfeb1180179682e`,
producer SHA256 `a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994`,
failed HIR for `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`.
The five reported diagnostics name `indirect_return` and `call_param_types`.
The extracted `emit_typed_function_value_call` also references caller-local
`args` and `callee`; all four belong to another method's scope.

The repair derives parameter and return types from the helper's explicit
`function_type` argument, validates ABI resolution and argument count, and uses
`arg_operands` and `call_span` for fallback checks and diagnostics. It preserves
legacy proven MIR function-pointer fallback and retained return ownership.
This is a direct implementation repair, not a temporary workaround.

Regression coverage extends `indirect_call_return_owner_spec.spl` with narrow
parameter signatures in both emitted call arms, arity rejection and unresolved
parameter rejection, alongside its existing return-owner tests. These scenarios
are not yet executed; no test success or linked binary is claimed here.

Implementation commit: `b114fbe355e257f6265b0fa9c738dcc21dea55b7` (not yet landed).
Original evidence is retained externally under
`phase3-validation-20261016/phase3-a174-1e93dca4-cli-bootstrap-cycle2/`, including
the three failed ledger rows and fatal diagnostics. Linked-output qualification
and landing remain pending.
