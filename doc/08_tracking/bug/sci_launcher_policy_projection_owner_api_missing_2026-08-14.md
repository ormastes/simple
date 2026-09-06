# SCI launcher policy projection lacks authoritative owner APIs

Date: 2026-08-14
Status: Open; launcher adapter fails closed

## Impact

`SimpleCompositionImageV1` application records can carry path-scoped
capabilities and file associations, but the launcher cannot safely admit either
field yet. The SCI adapter rejects the entire image before registry mutation
with a field-specific diagnostic. It does not create a second policy table and
does not let legacy defaults silently override SCI.

## Evidence

- `src/os/kernel/loader/artifact_manifest.spl:198-216` stores launch authority
  in `SimpleArtifactManifest`, but `required_capabilities` is only a `u32` rights
  mask. It cannot represent the path scope in `FileRead(/home)` or
  `FileWrite(/home)`.
- `src/os/kernel/loader/artifact_manifest.spl:374-389` exposes only
  `manifest_with_requested_rights`; there is no typed scoped-capability
  projection from SCI.
- `src/os/services/launcher/launcher_registry.spl:444-452` hard-codes extension
  associations in `launcher_associated_app_for_path`; there is no validated
  replacement/index API owned by that module.
- `src/os/services/launcher/launcher_composition.spl` therefore returns
  `SCI_LAUNCHER_MANIFEST_CAPABILITY_PROJECTION_REQUIRED` or
  `SCI_LAUNCHER_ASSOCIATION_PROJECTION_REQUIRED` before mutation.

## Unblock condition

1. Extend the existing `SimpleArtifactManifest`/launch-metadata projection with
   a versioned typed scoped-capability representation; do not add a rival
   manifest. Admission must validate every SCI capability and preserve its
   scope through spawn authority.
2. Add an owner API in `launcher_registry.spl` that atomically replaces an
   immutable, validated association index and resolves extension/MIME/protocol
   keys to registered application identities. Remove the hard-coded fallback
   once SCI migration is complete.
3. Add focused tests proving malformed/duplicate associations and unknown or
   over-ceiling capabilities reject before mutation, while valid policy is
   observable through the unchanged launcher/core artifact.

Shortcut projection is not blocked: the existing `launcher_register` owner API
already carries a fixed key and modifier mask, so the SCI adapter validates and
projects that field directly.

## Reload atomicity audit

The adapter validates record shape, policy support, duplicates, and replacement
capacity before mutation, then unregisters the prior SCI-owned names and
registers the replacement sequentially. For the current owner API,
`launcher_register` can fail only at its capacity check, which the adapter
precomputes for the supported path. A focused removed-app test proves successful
replacement semantics.

This is not a general transactional guarantee: there is no owner-level atomic
replace operation or rollback journal. If an unregister/register call later
acquires another failure mode, an unexpected commit-phase failure can leave a
partial replacement. Full atomicity is unblocked by an owner API such as
`launcher_replace_catalog_v1(validated_records)` that either commits all index
and registry changes or preserves the previous catalog, plus an injected
commit-failure test proving rollback.
