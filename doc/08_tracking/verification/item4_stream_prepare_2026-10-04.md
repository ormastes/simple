# Stream preparation verification

STATUS: FAIL — full item4/Phase 4 remains incomplete.

This prerequisite separates actual private image preparation from destination
publication. The existing one-shot API must delegate through the same owner,
retain no-clobber behavior and transfer cleanup exactly once. Successful publish
returns the existing committed result; failed cleanup remains retryable through
its owning object. Any publish/discard attempt retires publication permission.
No public mutable class is claimed to enforce affine security or cross-process
artifact authority. Lower-stage preparation failures still have the existing
text-only cleanup limitation; no invented recovery receipt hides that gap.

Acceptance uses real ELF inputs and filesystem stages, independent output bytes,
corrupt spill data, existing destination sentinels and real unknown-file cleanup
obstacles. Test intent precedes source implementation. Simple compilation,
SSpec/docgen, coverage, compiler/lib/MCP/native and NFR remain UNRUN.

The user requires native Windows/Linux/SimpleOS/FreeBSD/macOS execution with the
Simple linker explicitly selected, never made the hosted default. The new host
matrix distinguishes real hosted/guest execution from cross-generated formats.
No host row, worker admission or release-publication qualification is closed by
this preparation API. Existing UnsupportedBudget remains unchanged.
