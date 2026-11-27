# SCV structural storage v1

Manual mirror of
`test/03_system/app/scv/feature/scv_structural_storage_v1_spec.spl`.
Status: **NOT_RUN**; hand-maintained pending an admitted runtime for SPipe
docgen and `sspec-maintain`. This document records executable scenario intent,
not a passing execution receipt.

## Restore captured bytes through the normal commit caller

1. Capture BOM, invalid UTF-8, NUL and CRLF bytes in an unknown binary file.
   The normal file writer must retain raw bytes, link a structural root whose
   execution is `opaque`, and omit a CDC chunk map.
2. Create a tree and commit, then invoke public commit restore. Read the restored
   file as bytes and compare all seven bytes with the independent input array.
3. Remove the linked root, change the working destination, and invoke restore.
   It must report an error while preserving the working bytes.

Traces: REQ-SCV-STRUCTURAL-EXACT, REQ-SCV-STRUCTURAL-OPAQUE.

## Reconstruct the host partition without a grammar

1. Supply explicit fixture cursor spans for a comment and two identical
   identifiers, separated by CRLF and spaces. These fixture spans are not proof
   of a real provider execution.
2. Decode the byte DAG without loading any parser. The result must equal the
   exact input byte array, including all gaps.
3. Lower the decoder output budget by one byte. Reconstruction must fail.

Trace: REQ-SCV-STRUCTURAL-SPANS.

The unit SSpec additionally checks secure tamper detection, correct-hash schema
rejection, subtree-ID reuse, retention closure, oversized indivisible literals,
legacy/empty files, malformed/provider-error spans, and simulator rejection.
