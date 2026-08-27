# SimpleOS target-flow spec searches for a stale guard spelling

**Status:** Resolved

## Evidence

`test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl` searches
`llvm_target.spl` for the stale guard and return texts:

```text
if target == CodegenTarget.SimpleOS_X86_64:
return simpleos_triple
```

The committed source before the SFFI authority edit already used the computed
`if is_simpleos:` guard and returns the constructed `LlvmTargetTriple`
directly. The focused run executes seven examples: six behavioral target cases
pass and only this source-string assertion fails because the stale indices are
`-1`.

## Required repair

Replace the stale spelling check with an assertion over the actual computed
SimpleOS guard and its ordering before `get_host_os()`. Keep the behavioral
triple assertions. Do not weaken the case to a generic substring or mark it
passing without exercising target construction.

## Resolution

The assertion now searches for the exact computed `if is_simpleos:` guard and
the exact x86_64 SimpleOS `LlvmTargetTriple` return. It retains both ordering
checks plus the behavioral target construction checks.
