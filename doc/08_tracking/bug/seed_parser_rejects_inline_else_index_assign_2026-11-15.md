# Seed parser rejects `else: x[i] = v` single-line statement form

Status: worked around in two smux files; seed grammar gap still open.

`if c: a.push(v)` followed by `else: a[i] = v` fails in the Rust seed:
`parse: src/os/apps/smux/runtime_primary_control_service_v4.spl: Unexpected token: expected expression, found Assign at line 131, column 41`.
The inline `else:` body accepts an expression but not an index-assignment statement.

Impact: the caret CLI closure imports `os.apps.smux.server` (via `app/llm_caret/agent_workspace.spl`),
which imports the `_v4` smux services, so the seed could not even start caret
(blocked `caret_slang_local_hello_system_spec.spl`).

Worked around (pure syntax, multi-line `else:` block): `runtime_primary_control_service_v4.spl`,
`runtime_primary_geometry_service_v4.spl`.

Fix needed: seed parser should accept an assignment statement after inline `else:`.
