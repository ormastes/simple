# Unchanged SCV refresh repeats inventory publication work

Date: 2026-10-03. Scope: REQ-SCV-WARM-NO-EVENT-REFRESH.
Base: `49d4c083d82b79249b807b96e5e39f62a3cb603f`.
Implementation: source candidate; native/SSpec/performance **UNRUN**.

## Evidence and bounds

The original warm acquisition in `source_authority.spl` refreshes events, acquires
the snapshot, then binds its authority. Even with no events and the same cursor,
the refresh reads and canonical-decodes the complete inventory at four sites:
`inventory_events.spl` initial cursor binding, `compile_source_inventory.spl`
apply, publication under lock, and publication readback. Snapshot selection and
final authority binding add two more reads. Every read rebuilds the entries and
encodes them for canonical validation; publication also encodes its input.
That is six complete decodes and seven encodes per unchanged acquisition.

Snapshot reuse already avoids per-source materialization. Git's warm path still
observes current HEAD and scoped porcelain status, with a committed diff only
when HEAD changes. This report does not attribute observed minutes to any one
operation. A reported 101,922-file checkout is not evidence of 101,922 inventory
entries. No quadratic complexity or measured speedup is claimed.

## Selected correction and equivalence argument

After the existing Git, journal-prefix, and membership checks, only a non-cold
refresh with zero Git/filesystem events and byte-identical canonical v3 CURRENT
may avoid apply/publication/readback. Byte comparison includes Git HEAD, journal
count and digest, inventory generation/digest, and all membership digests. A
changed checkpoint, HEAD, legacy cursor, or noncanonical numeric spelling keeps
the original publication path.

The new production revalidation operation takes the existing publication lock,
compares CURRENT against the captured bytes, and rereads/hash-validates/decodes
the full referenced inventory before returning. It never trusts an in-memory
inventory instead of the blob. Pointer races, malformed generations, failed
locks and failed unlocks remain failures. Initial cursor binding is retained.

Independent review retained the publisher's SHA256 binding for CURRENT instead
of direct text equality: the native `rt_text_eq_any` implementation uses strcmp,
which stops at an embedded NUL. A behavioral negative control appends a NUL and
suffix after capturing the pointer, requires rejection without mutation, and
checks lock release after restoration. Only fixed-length hexadecimal digests
are compared by the new pointer check.

For this unchanged case, the old publication would return the same digest before
writing anything. The new path returns the same validated generation while
omitting two full decodes and three encodes: full acquisition falls from six to
four decodes and seven to four encodes. Other branches are unchanged. This is a
bounded reduction of repeated linear work, not constant-time warm startup.

The production library operation is shared with the event owner because the
publication lock belongs to SCV storage; it is not a test-only API. Existing
filesystem facades supply all access. No new raw OS operation is introduced.

## Acceptance and remaining validation

The integration specification and its mirrored manual cover an unchanged
refresh, a real tracked edit, inventory corruption, consumed-journal rewriting,
a source-free checkpoint, an empty Git commit, and stale expected-pointer
rejection after a newer publication. Tests compare actual rows/digests/cursors
and require rejected operations to leave authority intact. Cursor normalization
with a leading-zero row count also exercises the original publication fallback.

After independent review and the complete-byte pointer correction, both working
and populated staged direct-environment and numbered-artifact guards passed.
Staged whitespace check passed, and tracked executable specifications under
`doc/06_spec` count zero. These checks do not constitute a runtime or performance
PASS.

No compiler, native build, SSpec runner, or performance workload was launched.
Runtime validation and an admitted warm-startup measurement are required before
claiming execution correctness or a measured improvement. Root owns integration;
the parent review agent owns independent source review. Additional sidecars: N/A
for this bounded two-source-file correction.
