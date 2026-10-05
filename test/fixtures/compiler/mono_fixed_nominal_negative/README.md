# Fixed nominal argument frontend regression

Status: native UNRUN; queued under the shared admission policy.
Linked bug: mono_return_context_and_fixed_nominal_binding_2026-10-05.

Compile each entry separately using the actual candidate native-build path,
with the same admitted producer, options, runtime and source identity. The
negative fixture must not be compiled into the positive entry closure.

1. positive.spl must compile with exit 0 and its executable must run with exit
   0. This establishes that the generic syntax, constructor calls and toolchain
   work; generation logs or an absent output do not satisfy the control.
2. main.spl must fail during frontend type checking at line 14, the consume
   call. Preserve the actual diagnostic and require a type mismatch between
   the distinct declared nominal types Expected and Wrong (symbol IDs may be
   printed instead of names; resolve them through the actual HIR owner).
   Same field layout is intentionally insufficient for nominal compatibility.
3. Nonzero alone is not a pass. E-MONO-032/033, parser/import/infrastructure
   failures, crashes, and failed positive control are BLOCKED/FAIL evidence,
   never evidence that the frontend rejected the wrong fixed argument.
4. Do not add explicit generic arguments or alter either nominal type to make
   the negative case fail elsewhere. The original mono_context_repro/main.spl
   also retains its implicit generic calls for the result-context regression.

The new HIR spec case independently asserts that a typed lambda specializes
an array result, restores the enclosing scalar result context, and a later
outer return specializes the scalar rather than reusing the lambda result.
Neither source inspection nor this fixture definition is a native PASS.
