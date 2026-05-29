# Compiler CompileOptions Field Access - Design

## Problem

`FR-COMPILER-001` reported missing `CompileOptions.low_memory` and `CompileOptions.mode` field accessors in the self-hosted release binary. The local investigation shows these fields exist on `compiler.common.driver_core_types.CompileOptions`; the failure occurs when the resolver binds `CompileOptions` to the backend struct with the same short name.

## Design

The implementation is the import-resolution fix in `FR-COMPILER-002`: the HIR import pre-pass registers explicitly imported type names from the requested module before later declarations can shadow them. For `FR-COMPILER-001`, the observable contract is that an explicit import of `compiler.common.driver_core_types.{CompileOptions}` binds field reads to the driver struct.

## Test Strategy

Add a compiled system SPipe that imports `CompileOptions` from `compiler.common.driver_core_types`, calls `CompileOptions.default()`, and reads the driver-only fields named in the request.
