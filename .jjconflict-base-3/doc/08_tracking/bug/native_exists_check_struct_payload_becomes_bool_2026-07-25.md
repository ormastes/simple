# Native ExistsCheck uses its presence boolean as a struct payload

- **ID:** native_exists_check_struct_payload_becomes_bool_2026-07-25
- **Status:** SOURCE FIXED; native fixture wired, execution pending
- **Severity:** high for native `optional_struct.?.field` expressions
- **Lane:** native-build / Cranelift

## Reproduction

On hosted AArch64, compile an imported class getter returning `Evidence?`, bind
the result, then evaluate `evidence.?.marker`.

## Evidence

The refreshed Stage 3 caller correctly moves the class receiver into `x0`
before both zero-argument getters. After the optional getter returns, the
generated code calls `rt_is_some(evidence)`, zero-extends that `i1`, masks it
as though it were a tagged pointer, and performs the `marker` field load from
the resulting address. It never emits or calls `rt_unwrap_or_self`.

The resulting exit 132 (`field access on nil receiver`) is therefore downstream
of the getter and independent of receiver marshalling.

## Correction and verification

`ExistsCheck` now keeps a payload result local through its some/none merge and
attaches its inner struct provenance; it does not use the `rt_is_some` condition
as the expression result. `test/fixtures/native_exists_struct_payload_field/`
reproduces the imported getter form with the literal `evidence.?.marker` and
expects output `42`. It is registered in strict LLVM/Cranelift parity and the
shared cross-target object gate. The admitted pure-Simple candidate is not
available in this workspace, so this issue remains execution-pending.
