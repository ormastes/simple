# Flat pool fatal append diagnostics

Executable: `test/01_unit/compiler/frontend/flat_pool_append_diagnostic_spec.spl`.
Requirement: REQ-COMPILER-FRONTEND-001.

Build `test/fixtures/compiler/flat_pool_append_rejected_text.spl` with an admitted
native producer. Record the source commit/tree, producer SHA256, runtime archive
SHA256, backend, fixture SHA256 and hello receipt. Set
`SIMPLE_FLAT_POOL_APPEND_FIXTURE` to that compiled artifact, then execute the spec
with the admitted self-hosted test runner. Missing fixture input fails closed;
there is no interpreter or seed fallback.

The fixture first checks canonical escaping with valid text, then obtains the
runtime's NIL result from a bounds-checked empty text-array read. It verifies
that the runtime rejects this as text before passing it to the real encoder.
The spec requires fatal exit and the exact `text.value`, element 1, length -1,
return 0 diagnostic. A silently accepted value, missing diagnostic, wrong
position, or fixture precondition failure fails the test.

Native execution and the existing six-encoder canonical/round-trip suite remain
UNRUN for this patch. This is an observability regression, not proof that the
Ubuntu abort is repaired. Performance and the required core/MCP smoke gates are
also pending. Keep the PR draft until those gates are satisfied.
