# RT criticality driver severity routing

Executable spec:
`test/01_unit/compiler/semantics/rt_criticality_driver_routing_spec.spl`.

| Requirement | Scenario | Observable result |
|---|---|---|
| REQ-RT-OWNER-006 | Verified allocation with a supplied reason | Actual driver helper returns one fatal unbounded-allocation diagnostic |
| REQ-RT-OWNER-007 | Explicit robust allocation in migration epoch 1 | Actual driver helper emits the warning and returns no fatal errors |
| REQ-RT-OWNER-008 | Two claim identities resolve ambiguously against shared module path/name | Two diagnostics retain the individual claim keys |

Each scenario builds real HIR fixtures and invokes production validation or the
actual driver helper. The warning scenario's emitted output is also preserved in
the bounded diagnostic receipt, rather than inferred solely from an empty error
result. No test calls a helper-only substitute for the production policy.

Focused current-owner source-inline Stage 1 diagnostic: 3/3 PASS, peak job RSS
106268 KiB, final active job members 0. Supporting imports and cached bootstrap
producer are unadmitted. Real import/native/full-driver qualification remains
OPEN; these observations are not release evidence.
