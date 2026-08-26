# Minimal-Bootstrap Composition Development

This operator manual covers the implemented first slice: compile application configuration into an immutable SCI v1 image, validate it before use, replace renamed/removed catalog data in one launcher process, project supported shortcut metadata, reject unsupported policy authority, dispatch an in-process leaf provider through fixed-width descriptors, and inspect a conservative typed-edge rebuild decision. It does not claim native/SMF provider dispatch, an unchanged on-disk core hash, CAS execution, atomic rollback after an unexpected commit-phase failure, or full bootstrap elimination.

## Compile and inspect one immutable composition image

Requirement coverage: REQ-001, REQ-002, NFR-001.

1. `compile_composition` — parse normalized SDN application configuration and encode SCI v1.
2. `check_composition_image` — require a validated image, one expected app record, and canonical bytes.

Expected outcome: reordered equivalent input encodes identically; malformed magic, bounds, overlaps, required sections, or digests fail closed.

## Compile CLI command and provider selection as data

Requirement coverage: partial REQ-001, REQ-002, REQ-005, and REQ-007.

1. Declare one versioned CLI interface group and ABI digest.
2. Lock one formatter provider artifact digest and capability requirement.
3. Bind `cli.format` to that provider.
4. Store `format`, alias `fmt`, and summary metadata in SCI.
5. Encode, authenticate, decode, and resolve every reference.

Expected outcome: command metadata and provider selection round-trip through a
required, independently digested SCI section without importing formatter code.
This proves compiled composition data, not root-CLI dynamic dispatch or the
zero-compiled-module build receipt.

## Reload catalog data without replacing launcher code

Requirement coverage: partial REQ-008.

1. Compile the original app name.
2. Compile the renamed app record.
3. `load_unchanged_core` — load both validated projections in one launcher process.

Expected outcome: both records become observable without restarting or recompiling launcher source. This is not yet the stronger on-disk core-artifact hash proof required for complete REQ-008/NFR-008 acceptance.

Focused unit evidence also loads a two-record image followed by a one-record
replacement and requires the omitted record to disappear. The supported path
prevalidates the complete image before retiring the prior SCI projection. It is
not a transactional rollback guarantee if a commit-phase owner call fails
unexpectedly after retirement.

## Project supported launcher policy and reject unsupported authority

Requirement coverage: partial REQ-003 and REQ-008.

1. Compile one app with `Ctrl+Meta+E`.
2. `check_launcher_policy_projection` — load it and inspect the launcher-owned
   key/modifier fields.
3. Compile a path-scoped `FileRead(/home)` capability and require
   `SCI_LAUNCHER_MANIFEST_CAPABILITY_PROJECTION_REQUIRED` before mutation.
4. Compile an extension association and require
   `SCI_LAUNCHER_ASSOCIATION_PROJECTION_REQUIRED` before mutation.

Expected outcome: the shortcut projects through the existing registration
owner. Capability and association images fail closed because the canonical
manifest cannot yet preserve scoped capabilities and the launcher registry has
no association replacement API. The exact unblock conditions are recorded in
`doc/08_tracking/bug/sci_launcher_policy_projection_owner_api_missing_2026-08-14.md`.

## Query and dispatch one leaf command provider

Requirement coverage: partial REQ-005, REQ-007, REQ-014, REQ-015.

1. `dispatch_provider` — register one in-process leaf command provider.
2. Query its CLI interface through fixed-width numeric descriptors and handles.
3. Enforce interface major, descriptor length, and capability bits.
4. Execute the leaf command and inspect its bounded output receipt.
5. Confirm native and SMF modes return `SIMPLE_PROVIDER_NOT_PROCESS_CALLABLE`.
6. Activate a replacement generation while the prior generation is pinned;
   release the pin and sweep only after the old handle is no longer live.

Expected outcome: the in-process provider returns `formatted:notes.spl`;
dynamic modes fail closed; a retired in-process generation remains available
until its final pin is released. This is an executable contract and generation-
owner proof, not cross-library loader evidence.

## Explain conservative rebuild decisions

Requirement coverage: partial REQ-011, REQ-012, NFR-011.

1. `explain_rebuild` — construct the scheduler-owner receipt for an unknown compatibility result.
2. Confirm reuse is prohibited.
3. `check_rebuild_receipt` — require the smallest non-empty rebuild closure and rebuilt count.
4. `check_bootstrap_reason` — confirm configuration work does not select bootstrap.

Expected outcome: `Unknown` never authorizes reuse. The decision records changed
interface groups, relevant digest deltas, conservative rebuilt/reused counts,
bootstrap requirement/reason, and whether cache evidence is available. Current
evidence validates decision semantics; authoritative compiler closure receipts,
dependency artifact inputs, CAS reuse, and measured rebuild containment remain
open.

## Open implementation rows

- Native/SMF process-callable provider loading through `SimpleProviderQueryV1`.
- Exact unchanged-core artifact digest before and after SCI-only compilation.
- Authoritative `SimpleArtifactManifest` projection for scoped capabilities and
  a launcher-owner association index. Shortcuts are supported.
- Transactional launcher reload rollback when a commit-phase owner call fails
  after the previous projection has been retired.
- Authoritative imported-closure receipts, declared dependency-artifact inputs,
  and measured scheduler/CAS reuse evidence.
- Pure-Simple self-hosted SPipe execution and performance/RSS measurements.
