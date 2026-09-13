# Interpreter registry references missing fail-closed adapters

**Date:** 2026-09-09  
**Status:** Fixed in the physical paged-KV activation lane

## Symptom

The canonical Stage-2 bootstrap stopped while compiling the Rust seed with 21
`E0425` errors. The interpreter registry referenced an OwnedProcess V3 adapter
and CPU-affinity/AVX2 adapters that did not exist in their owner modules.

## Resolution

The owner modules now provide explicit error-returning adapters. Interpreter
execution cannot fabricate native process leases, affinity ownership, or AVX2
execution evidence; all registered names resolve deterministically and fail
closed with a native-runtime requirement.
