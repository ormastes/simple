# Traceability Progress Report

Date: 2026-03-28

## Summary

Traceability work is partially implemented. Core source-to-test path mapping and trace ID extraction are in place, and the traceability module now includes manifest-based helper entry points intended to reduce interpreter-specific failures during focused tests.

The main remaining blocker is the Simple interpreter, not the high-level traceability design. The focused traceability analysis examples still fail during execution with runtime semantic errors, so the feature is not complete and the checker is not yet validated end to end.

## Implemented

- Added traceability helper exports in [src/app/traceability/__init__.spl](/Users/ormastes/simple/src/app/traceability/__init__.spl).
- Added manifest/default-root helper functions in [src/app/traceability/core.spl](/Users/ormastes/simple/src/app/traceability/core.spl).
- Updated the focused spec in [test/unit/app/tooling/traceability_spec.spl](/Users/ormastes/simple/test/unit/app/tooling/traceability_spec.spl) to use manifest-style inputs instead of direct virtual-file arrays.
- Source mapping helpers are present for:
  - source file to unit spec candidates
  - source directory to integration/module spec candidates
- Text parsing helpers are present for:
  - relative path extraction
  - `REQ-*` and `NFR-*` identifier extraction
  - date-suffixed slug normalization

## Current Failures

The focused command:

```text
bin/simple test test/unit/app/tooling/traceability_spec.spl
```

still fails in the traceability analysis section.

Current failure pattern:

- `semantic: invalid operation: cannot index value of type i64`

This affects the analysis examples that should verify:

- uncovered requirement IDs
- legacy requirement root warnings
- raw spec links from docs
- missing unit/module tests for opted-in source roots

## What Was Learned

- Arrays of structs and some imported composite arguments appear unstable under the current interpreter path.
- Rewriting test inputs from `VirtualFile` arrays to manifest text reduced some boundary complexity but did not eliminate the runtime failure.
- The remaining issue is likely inside interpreter handling of imported helper calls or collection/indexing semantics, not in the intended traceability rules themselves.

## Next Work

- Reduce the analysis/count path to interpreter-safe primitive operations only.
- If that still fails, move the fragile counting/test helper boundary behind a different implementation path rather than continuing to layer Simple-side wrappers.
- Re-run the focused traceability spec until all helper and analysis sections pass.
- After the focused spec passes, validate CLI/build integration again.

## Version Control

Previous pushed progress commit:

- `7403c2f2` — `test: adapt traceability spec to manifest helpers`
