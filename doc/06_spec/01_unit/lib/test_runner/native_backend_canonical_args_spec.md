# Canonical Test Runner Native Backend Arguments

Source: `test/01_unit/lib/test_runner/native_backend_canonical_args_spec.spl`

## Scenarios

1. The live canonical parser accepts `--native-backend cranelift`, selects
   native execution, disables result caching and session routing, requires
   assertion evidence, and forwards the backend to a child test process.
2. `--native-backend=llvm` keeps native execution and the safeguards even
   when later flags request a different mode or session routing.
3. Missing and unsupported backend values fail validation before execution.

The executor's native build and artifact provenance require separate
source-bound Stage2 verification; this unit spec covers argument ownership.
