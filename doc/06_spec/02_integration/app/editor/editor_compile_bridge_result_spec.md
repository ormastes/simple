# Editor optimized compile bridge: failure result

**AUTHORED_UNRUN — not a generated PASS manual.**
Requirement: REQ-EDITOR-JIT-001.
Executable: `test/02_integration/app/editor/editor_compile_bridge_result_spec.spl`.

Request compilation of a missing source through the actual optimized public
facade, then inspect its returned tuple. The success field must be false and the
diagnostic must contain text. The three scenarios cover optimization levels
zero, two, and an invalid level; none may treat an invalid tuple handle as a
successful return from the bridge.

Native/JIT and interpreter runs must be recorded separately with admitted
producer and linked-runtime identities. The interpreter has its own compiler
host implementation; passing there does not qualify the standalone Rust runtime
export. This manual does not assert that the editor starts, that native
compilation works, or that the current C provider implements this bridge.

Direct Rust tests additionally check tuple length, boolean tagging, and the
explicit unavailable-driver diagnostic. Both test sets remain unrun. Docgen and
its zero-stub gate are blocked on the shared admitted-runtime prerequisite.
