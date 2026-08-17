# Stage 3 exits 139 after post-folded-constant diagnostics

- **Bug ID:** `stage3_post_folded_const_diagnostics_sigsegv_2026_08_14`
- **Status:** OPEN
- **Severity:** P0 bootstrap blocker
- **Date:** 2026-08-14

## Preserved System evidence

Clean detached worktree `/tmp/simple-stage4-mir-0e900` is pinned to
`0e90035ad3a`. An admitted Stage-2 compiler and runtime from the read-only
qemu-matrix lane compiled current `src/app/cli/bootstrap_main.spl` with LLVM,
one thread, `core-c-bootstrap`, `dynload`, and
`SIMPLE_NO_STUB_FALLBACK=1`, using isolated output/cache paths.

The run remained CPU-active for roughly seven minutes, peaked near 7.7 GiB
RSS, emitted no object, and terminated with exit 139. Its final output was:

```text
[bootstrap-error-count] source_idx=0 point=entry count=0
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=9
[bootstrap-error-count] source_idx=1 point=entry count=9
[bootstrap-error-count] source_idx=1 point=post-lowering count=9
[bootstrap-error-count] source_idx=1 point=post-diagnostics count=95
[bootstrap-error-count] source_idx=2 point=entry count=95
[bootstrap-error-count] source_idx=2 point=post-lowering count=95
[bootstrap-error-count] source_idx=2 point=post-diagnostics count=98
[hir-field-type] struct=CompiledUnit field=entry_point actual=2589120870
[hir-field-type] struct=BackendError field=span actual=2589120870
```

The `actual=2589120870` rows are known benign Optional-variant probes and are
not a root-cause claim. The important boundary is diagnostic growth from zero
to 98 across the first three sources followed by SIGSEGV before object output.

The folded-module-constant diagnostic is absent, proving the preceding MIR
category crossed its failure frontier. This new category must preserve the
exact System evidence, reproduce at the smallest owning Integration boundary,
then add same-mechanism System/Integration/Unit scenarios with 100% branch
coverage for the changed unit owner before a fix is accepted.
