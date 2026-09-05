# wine_process_tls_dispatch_spec pre-existing RED — missing VM write-readback evidence token

- Date: 2026-08-27
- Spec: `test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl`
- Status: OPEN (pre-existing at HEAD, proven below)

## Evidence
HEAD restore (`git show HEAD:<spec>`) run 2026-08-27:

    Results: 2 total, 1 passed, 1 failed

Failing scenario: "should require PEB/TEB VM byte-write readback before TLS
callback dispatch record" — the gate evidence string lacks the expected token
`VMWriteReadback:PEBTEBLayoutBytes...` (full expected/actual pair in the run
log; the actual evidence enumerates gate names but no VMWriteReadback marker).

## Context
Recorded during the sspec modernization batch. The only edit applied was
re-indenting a misplaced `# @req REQ-037` comment into the `it` body
(TRC-003) — comment-only; HEAD baseline above proves the red predates it.
Spec left RED per testing rules (score rose 49 -> 89 on the traceability fix;
the failing assertion was not weakened).

## Unblock condition
The PEB/TEB write-gate path must emit the documented
`VMWriteReadback:PEBTEBLayoutBytes*` evidence token (or the spec's expected
token must be reconciled with the gate's actual evidence vocabulary by the
feature owner).
