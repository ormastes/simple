# Managed parser V2 compatibility contract

Status: source-authored manual; tests and native qualification **UNRUN**. This
manual records intended checks, not passing evidence. Requirements: REQ-IM-008,
REQ-IM-012, REQ-IM-016, NFR-IM-004.

1. Construct frontend identity from independent parent identity, complete prior
   cache scope, actual feature digest and capture policy. Round-trip the exact
   nine-string canonical single-line SDN array. Reject foreign versions,
   whitespace changes and malformed field counts.
2. Change each prior identity dimension, worker image digest, OS, architecture
   and CPU independently. Observe a different derived cache key.
3. Supply one launch identity assignment. Reject missing and duplicate
   assignments, including differently cased duplicate names.
4. Decode the actual FPC header shape. Compare compatibility against SHA-256 of
   its exact scope substring excluding FPC/flat-codec prefix. Changing the lane
   changes compatibility; unsupported optimization settings reject.
5. Parse the closed `grouped-run-v2` CLI argument set. Every pin is mandatory;
   missing, empty, duplicate and unknown options reject. No receipt or manifest
   field provides a default expected pin.

Companion qualification specs exercise actual file hashing and run admission
against mechanically created pinned files. Those fixtures do not establish
native worker provenance or executed parser qualification.

Real process qualification is a separate Windows execution gate: a fresh pinned
parent parses the clean fixture; an explicit-env, memory-bounded worker parses
error / captured-write / clean / error modules twice. Warning policy requires
located Warning records and real artifacts, no reusable receipt or authority,
stable diagnostic identities and fresh parsing on the second action. The clean
artifact must match actual parent output and reuse on the second action. Only
after successful bounded shutdown and tree cleanup can an issuer return a V2
identity. These process checks have not been executed in this change.
