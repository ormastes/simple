# SimpleOS target-flow spec searches for a stale guard spelling

**Status:** Open

## Evidence

`test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl` searches
`llvm_target.spl` for the exact source text:

```text
if target == CodegenTarget.SimpleOS_X86_64:
```

The committed source before the SFFI authority edit already used the computed
`if is_simpleos:` guard. The focused run executes seven examples: six behavioral
target cases pass and only this source-string assertion fails because its index
is `-1`.

## Required repair

Replace the stale spelling check with an assertion over the actual computed
SimpleOS guard and its ordering before `get_host_os()`. Keep the behavioral
triple assertions. Do not weaken the case to a generic substring or mark it
passing without exercising target construction.
