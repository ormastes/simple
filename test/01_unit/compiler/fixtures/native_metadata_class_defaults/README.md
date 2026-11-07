# Native metadata-only class regressions

Build each `main.spl` as a separate LLVM native entry, then execute its output.
The source-only owner module in empty_array, nonempty_array and dictionary has
no callable members. Its metadata must survive imports while its empty final
MIR receives an objectless result. The caller must execute every assertion.
`callable_class` is a counterexample: its owner must retain a real object and
the call must return 17; it must never be classified as metadata-only.

Expected assertions: empty_array 1, nonempty_array 4, dictionary 3,
callable_class 1. Each prints its exact pass marker after the assertions.

Status: UNEXECUTED against this change. The historical 38dd producer passed
Hello, but all three original data-class fixtures failed later at object
generation with `MIR module has no functions or static data`; none executed.
Their MIR stages completed without the earlier ArrayLit relocation crash.
Retained evidence: build/review/item5-provider-default-qualification-20261107.

Admission still requires successful typed lowering, unchanged source identity,
and final MIR with no functions, statics or constants. Unknown class
attributes, callable members, volatile/fixed-address fields, actors and
ordinary function bodies remain ineligible for this classification.
