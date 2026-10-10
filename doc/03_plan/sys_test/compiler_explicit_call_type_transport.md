# Explicit direct-call transport acceptance

1. Real frontend/HIR assertion: absent<i64>() has one signed 64-bit explicit
   type and zero value arguments. Authored spec: explicit_call_type_arguments.
2. Native return-only integer and text calls compile with zero unresolved
   generics, execute with exact success output, and retain comparison behavior.
3. Invalid explicit generic arity rejects compilation and produces no object.
4. Real MC/DC closure compiles on ARM and RISC-V; ARM executes and RISC-V
   object header proves EM_RISCV. Report unavailable RISC-V execution honestly.
5. Nested/optional type parsing, const-generic rejection, no metadata inheritance
   on chained calls, and flat reset/clone/cache transport remain covered.
6. Native generation includes Type traversal and semantic encoding, and never
   enables semantic caching of opaque block arena ids. Generator evidence PASS.
7. Working/staged environment guards and generated-manual layout are clean.
8. Required compiler/core/MCP/LSP verification and canonical Stage 2 gates pass
   before the release PR can claim bootstrap admission or start Stage 3/4.

Native compiler preparation is not test execution. Keep all candidate failures,
use at most three repair/verify cycles for each scoped defect, and do not repeat
green checks without relevant changes.
