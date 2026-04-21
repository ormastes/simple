# Compiler CompileOptions Field Access - System Test Plan

## Request

Cover `FR-COMPILER-001`: the self-hosted compiler must resolve field reads on the explicitly imported driver `CompileOptions` instead of the backend struct with the same short name.

## Test

`test/system/compiler_compile_options_field_access_spec.spl`

## Assertions

- `CompileOptions.default().input_files.len()` is readable and equals `0`.
- `CompileOptions.default().low_memory` is readable and equals `false`.
- `CompileOptions.default().mode` is readable and equals `CompileMode.Jit`.
- Driver-only fields such as `backend` and `smf_output_mode` remain readable.

## Verification Command

`bin/simple test test/system/compiler_compile_options_field_access_spec.spl`
