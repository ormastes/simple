# Lazy generic body index proof model

`LazyBodyIndex.lean` models a stable module function sequence and ordered impl
sequence. It proves output equivalence between eager indexed lookup and an operational
lazy memoized construction, a one-build upper bound, and zero builds for modules
with no generic impls. Lookup is defined to model last-write-wins symbol lookup;
that definition is not a proof of the production dictionary implementation. Missing method symbols yield `none`; nongeneric impls contribute
no outputs.

The model assumes stable module function/impl order and stable symbol IDs. It is
not a proof of refinement to production HIR, `Dict`, allocator, or iterator
semantics. The repo-pinned Lean version is 4.30.0. `lake build` compiled the
model successfully; the external run log is
`/home/yoon/dev/phase3-goal-continuation-20261013/robust-generic-formal-20261014/lake-build.log`. The first invocation found an
import-order syntax error, which was corrected before the successful build.

Run the pinned toolchain with `lake build` in this directory. This uses only Lean Std; no external proof library is required.
