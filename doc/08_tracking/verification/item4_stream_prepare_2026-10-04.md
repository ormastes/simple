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

Source outcome: private preparation, one-attempt publication and independently
retryable cleanup are implemented. Four executable scenarios include failure of
publication together with failure of both cleanup owners. Independent review of
source `775e2e948558` and acceptance through `57fc993d7ac` found no P0/P1 issues;
root integration preserved all seven patches unchanged during rebase onto
`f1b949825acb4eeb1d3449f45f083b860abcc7c1` (range-diff all equal).

Structural checks passed: whitespace, direct-env working/staged guards, numbered
artifact guard, and zero executable specs under the manual tree. The committed
test-tree delta passed with 3151 inherited offenders and zero new offenders.
Evidence: `C:/dev/simple/.git/item4-stream-prepare-preexisting-offenders.txt`.
These are structural/source results only, not executed Simple acceptance or
permission to publish a qualified release. Full verification remains FAIL.
