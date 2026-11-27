# Native black-box per-call identity regression

Source: `test/01_unit/lib/crypto/rt_black_box_concurrent_identity_spec.spl`.
Status: **AUTHORED_NOT_RUN**; this manual was authored without docgen execution.

This regression targets BUG-RT-BLACK-BOX-SHARED-SINK-001. Use an admitted native
test runner whose link/provider provenance establishes that the changed C
`rt_black_box` MSVC or generic branch is selected. Record compiler, flags, target,
runtime archive/object hashes and resolved symbol provider. Do not accept the
Rust strong symbol, interpreter implementation, cached pre-fix C object or the
unchanged GNU inline-asm branch as coverage of the corrected branches. Do not
force a platform macro onto an incompatible toolchain to manufacture coverage.
The current campaign authorizes no native build or execution.

1. Call the primitive directly for zero, one, minus one, signed i64 maximum and
   minimum, positive/negative values beyond 32 bits, and a further nonzero value.
   Every optional result must be present and equal its input. Nil, zeroing or
   constant-return substitutes fail at least one input class.
2. Obtain the actual native thread identity. Start two OS workers with different
   input phases. Each worker must have a positive identity distinct from the
   test thread and increment a real atomic ready count before waiting for release.
   The parent releases only after both workers are ready. Waiting is bounded;
   inline execution or failed admission produces a failure, never a skip/pass.
3. Each worker makes 65,536 direct calls cycling through all eight input classes.
   A missing or mismatched primitive result returns a failure outcome immediately.
   No worker asserts or modifies ordinary shared state.
4. Join both workers, then retire both atomic handles, before asserting results.
   Require successful rendezvous, two present positive worker outcomes, and
   worker identities distinct from the parent and each other.

The expected functional result is per-invocation identity. Stress scheduling
cannot guarantee that the old race manifests on every run. Separate actual
data-race-detector coverage of the affected provider remains outstanding. This
spec does not prove optimizer opacity, timing behavior, constant-time comparisons,
or authentication correctness. Both scenarios, native linking and provider
qualification remain **NOT_RUN**.
