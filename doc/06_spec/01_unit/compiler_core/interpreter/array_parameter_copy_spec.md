# Interpreter array parameter copy

Requirement: `REQ-INTERP-ARRAY-PARAM-VALUE`.
Executable: `test/01_unit/compiler_core/interpreter/array_parameter_copy_spec.spl`.

The executable specification calls the production `val_copy_for_parameter`
helper and the real interpreter value arena. It verifies independent array
storage after append and replacement, independent nested arrays, shared
registered class identities, copied registered value structs with array fields,
and unchanged scalar identities plus independent empty arrays.

Parameter binding in `eval_function_call` calls this helper. Value structs
recursively use it for their fields, preserving class references while copying
array storage. The helper does not replace the general struct copy gate.

## Verification evidence

Release base: `c4cd4530c1d4e61d74ce669d54b9e26c0d625a44`.
Stage 1 cached bootstrap producer SHA-256:
`6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`.

Diagnostic status: **BLOCKED**, declared 5 / executed 0. The explicit AST
owner import encounters the existing `windows_redirected_process.spl`
`Unexpected token: expected Fn, found Colon` parse failure. No assertion
is marked passed, skipped, or weakened. Zero compiler rebuilds.

Pure Simple compiler/core/library/MCP qualification and runtime smokes remain
pending because the release runtime is unavailable on this host. This change
is a draft repair, not a qualified release admission.
