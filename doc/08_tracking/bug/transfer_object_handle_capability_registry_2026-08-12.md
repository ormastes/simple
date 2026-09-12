# Transfer object-handle capability registry blocker

**Status:** OPEN (unverified 2026-09-12)

## 2026-08-12 owner-scoped registry slice

Implemented the common pure-Simple owner authority in
`src/lib/common/structural/transfer/object_handle_capability_registry.spl`.
It binds `(region_id, generation, ownership_token, owner_context)` in a fixed
capacity slot table, mints monotonic non-zero opaque tokens, checks the
canonical `TransferEnvelopeV1` boundary before acceptance, consumes a live
capability on successful validation to reject replay, and supports owner-only
revocation. It stores no raw pointer or dereferenceable address. Focused unit
coverage is in
`test/01_unit/common/structural/transfer_object_handle_capability_registry_spec.spl`.

The authority is common/pure-Simple; no Rust adapter is required for this
owner-scoped contract slice.

`TransferEnvelopeV1` now fails closed for process and remote `ObjectHandle`
payloads unless they carry the immutable-share mode plus non-zero region
generation and ownership token. This is a structural wire gate, not proof
that the capability was minted by the owner.

The receiving runtime still needs an owner-scoped capability registry (or an
equivalent authenticated capability verifier) to bind `(region_id,
generation, ownership_token)` to an immutable object, enforce revocation, and
prevent replay. This patch intentionally does not invent a global registry.
Until that owner-side validation exists, process/remote object handles remain
admission-safe but not fully lifecycle-verified; inline and encoded-copy
payloads remain available.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
