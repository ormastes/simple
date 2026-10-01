# Cooperative namespace selected-head restart/recovery test plan

Status: authored structural plan; all dynamic rows remain `MissingEvidence` until the host authority supplies the frozen integration seam and owner-issued receipts. Final evidence reviewer: Astra.

## Scope

The executable matrix is `test/03_system/app/compiler/feature/cooperative_namespace_selected_head_spec.spl`. It covers crash/restart at the before/after boundaries for immutable blob sync, journal admission, selected-head replacement, and parent-directory sync; complete trailing records; stale and independent-process writers; projection rebuild; and fail-closed GC. Fixture rows live in `test/fixtures/cooperative_namespace_selected_head/recovery_matrix_v1.txt`.

It excludes implementation of the namespace issuer, journal/CAS, selected-head publisher, DB engine, and GC. It does not accept logical durability, a direct filesystem mock, an in-process model, a static result, or the Rust seed.

Five supplementary component controls call the existing frozen diagnostic
surfaces: selected-head name/host availability, exact selected-prefix matching,
writer/head revalidation, durability-order classification, and fail-closed GC
issuance. They are executable component regressions, not physical authority or
acceptance evidence.

## Required live harness

The host must expose a process-safe operation that accepts the fixture row, terminates an actual publisher process at that named boundary, restarts a new process, and returns an owner-issued receipt containing: operation digest, selected-head revision, accepted journal bytes and prefix digest, typed closure digest and verifier-registry digest, writer incarnation, process identities, projection result, GC action count, and exact source/runtime/fixture hashes. The test binds to the frozen host signature only; it must not reimplement this operation in SSpec. This is process-restart evidence; a separately qualified storage-fault/power-loss provider is required for physical cache-flush durability.

## Pass criteria

For rows 001–008, restart selects either the old operation or the exact interrupted operation where the fixture permits it, never a mixed or later record-derived root. Before head replacement, journal admission may retain an exact operation only for reissue and must retain the old selection. Before directory sync, an old-or-new result is indeterminate and cannot be acknowledged as durable success. Row 009 proves a complete trailing record is ignored. Rows 010–011 prove writer exclusion across distinct processes. Row 012 proves the DB projection is derived from selected durable authority. Row 013 proves GC makes no destructive action if any reader, lease, or pin contribution is missing. Astra accepts the retained live receipt set before any availability or publication claim.

## Execution order

1. Host owner freezes the public integration signature and fixture-root use.
2. Run diagnostic controls on the qualified self-hosted native runtime and retain their component receipt separately from physical evidence.
3. Run each matrix row once only after the host exposes a crash/restart provider.
4. Regenerate the manual; retain the command transcript and receipt hashes.
5. Astra reviews boundary coverage and owner/receipt identity.

No runtime result is currently recorded. This plan grants no L08 acceptance credit and leaves the availability flags false.
