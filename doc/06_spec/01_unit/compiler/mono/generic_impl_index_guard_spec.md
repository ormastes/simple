# Generic impl indexing guard

Status: UNRUN. Source: `test/01_unit/compiler/mono/generic_impl_index_guard_spec.spl`.

Four production-API cases verify no-impl free generics, unchanged nongeneric
impl HIR, mixed nongeneric/generic impl registration, and trait-impl rejection.
Retained and archive-request modes are checked where applicable.

The intensive native fixture additionally has 30 workload rows and 30,720 actual
collector calls, default-expression checks, selected template-state/body
fingerprints, HIR immutability checks, and raw monotonic timing samples.
Selected fingerprints do not cover every pass field. Whole-process RSS is
not a collector allocation measurement.

Require actual baseline and candidate compilation and execution with identical
producer/runtime/workloads, matching correctness fingerprints, and the
predeclared memory/performance criteria in the validation plan. No executable,
missing success marker, or failure to compile is not a PASS. The separate
whole Phase3 object-compilation landing condition must also pass.
