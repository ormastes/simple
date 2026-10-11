# Generic exception traversal candidate

Status: source-reviewed candidate; execution UNRUN.

HIR body substitution did not handle `TryCatch` or expression `TypeTest`.
The post-monomorphization verifier also did not handle `TryCatch`. A generic
type in a catch pattern/filter/body or finally block therefore could not be
substituted and checked through the complete exception expression.

The candidate substitutes the try block, each present catch pattern and type
filter, every catch body, and the optional finally block. It traverses the
operand of a type test while retaining its literal target-name metadata.
The verifier visits the same typed exception edges and honors presence flags.

`generic_exception_traversal_spec.spl` first requires five unresolved type
occurrences to be counted, then independently checks each substituted edge
and a clean verifier report. Additional cases cover absent metadata/finally
and type-test operands. These tests have not run on an admitted self-hosted
runtime. Exception execution, native memory behavior, generic type-name tests,
and generated visitor consistency are separate obligations; none is claimed
proven by this source change.
