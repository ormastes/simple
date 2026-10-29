# BuildRunner Cranelift function-handle diagnosis

Stage: scoped diagnostic change reviewed; three native bridge tests passed.

Exact manager failure remains open. The bridge preserves underlying
declaration errors and distinguishes invalid import state without changing
the exported failure ABI. Three native Rust regression tests executed on
Linux arm64: 3 passed, 0 failed after the assertion matched the retained
Cranelift debug type names. Canonical Linux seed/P2 rebuild will consume the
reviewed source in an isolated lane; no stale binary pass is reused.

Owned debugger attach stopped before codegen coverage, and producer identity
refused a replacement launcher. Those are failed diagnostics, not successful
compiler executions. No process-spawn interposition or strict-policy bypass
is used. The user explicitly authorized continued work after the original
six-build budget; future builds require a changed diagnostic or implementation.
