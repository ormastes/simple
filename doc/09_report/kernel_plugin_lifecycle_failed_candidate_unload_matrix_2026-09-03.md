# KPF Failed-Candidate and Unload Matrix

**Date:** 2026-09-03  
**Requirement:** REQ-KPF-007 lifecycle safety  
**Status:** PASS for the focused portable lifecycle matrix

## Covered behavior

- Invalid-identity candidate publication fails without replacing the active generation.
- Generation-capacity exhaustion fails without replacing the active generation.
- Pin-capacity exhaustion is explicit and leaves the first pin valid.
- An active generation cannot be collected.
- Rollback is restricted to the immediate retired predecessor.
- The rolled-back candidate can be collected only after it is retired and unpinned.
- Repeated collection and repeated pin release are rejected as stale-handle operations.
- Existing cancellation/completion/deadline arbitration and request-slot ABA checks remain covered.

## Evidence

```text
deadline_cancellation_publication_spec.spl: 10 passed, 0 failed
deadline_cancellation_publication_mutation_spec.spl: 3 passed, 0 failed
runtime: admitted pure-Simple macos-arm64
runtime_sha256: 277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767
```

The mutation gate specifically rejects an implementation that collects the active generation or accepts reuse of a released pin handle. This closes the focused failed-candidate/unload matrix, but does not claim completion of crash-loop, cross-placement parity, or long-run no-allocation requirements.
