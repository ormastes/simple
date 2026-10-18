# BUG-2026-10-18-FINGERPRINT-NIL-SHA-ADMISSION

Status: source repair; native qualification UNRUN. Bug database reconciliation
pending because the normal database tool is unavailable in this session.

The repaired ee3 producer's Hello attempt retained a 631-byte AMD64 COFF object
with SHA256 `6371b7312479cf686061939f267f4f695a43a80a3e03c03fdbd36e9582df6550`.
Its capsule receipt had six LF-separated rows, correct size and path, and an
empty digest row. The original object path was 262 characters. Evidence is
preserved separately under the producer qualification owner; no retry or live
cache mutation is part of this source repair.

`rt_file_hash_sha256` returns native nil on failure, although the Simple extern
is declared `text`. `FileFingerprint.from_file` checked only equality with empty
text. Native equality distinguishes nil from empty text, so a failed hash could
be retained as `content_hash`. The receipt writer and its initial verifier use
the same runtime hash path; the later cold object gate independently hashes the
bytes and correctly rejects the empty receipt digest. The Windows raw hash
opener uses narrow `fopen`; its long-path repair is owned by a separate lane.
This change neither proves the exact open error nor changes runtime behavior.

Admit fingerprints only for exactly 64 lowercase hexadecimal bytes. Length is
checked before indexing, so the native nil text length (-1) fails closed. No
shell hash fallback, permissive receipt handling, or fabricated digest is added.
No suitable general SHA validator is exported by the already imported canonical
identity/crypto owners; the small predicate remains with fingerprint admission.

Caller audit: native object/source admission and native no-op callers already
reject nil; backend build treats it as a miss; record helpers skip publication;
cache validity helpers reject it. Two incremental callers needed correction:
DependencyEntry.needs_recompile must not accept a failed dependency hash, and
BuildCache.detect_changes must not silently skip a failed source fingerprint.
Existing cached paths that disappeared are Deleted; existing paths with failed
hashes are Modified; previously uncached requested paths are Added. The existing
membership-based deletion pass remains unchanged.

Regressions use actual missing-file runtime hashing, empty/binary file reads with
known SHA256 values, unchanged source control, removed cached/new source inputs,
and a removed dependency. Scalar validator negatives cover length, uppercase,
and invalid hex. Missing-dependency I/O can fail at the earlier size check; it
is not claimed to isolate the new post-size nil branch. The raw native failure
case specifically checks the real FFI result rather than a synthetic nil text.

All new Simple specs, core checks, and full native qualification are UNRUN until
a qualified pure-Simple CLI is admitted. Static source review is not native PASS.
