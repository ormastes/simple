# Provider admission from persisted runtime package metadata

**TEST_BLOCKED — authored manual, not generated execution evidence.** The 17
scenarios were added on branch `work/item5-test-20261001`, based on Item 5 PR
2149 head `4efd8885ded0cf87ad1b89b6ff96e3f46c9d68dc`. No admitted self-hosted
POSIX runner is available. RED, GREEN, SPipe execution, docgen, inline expansion,
and zero-stub scoring have not run. No runtime PASS or release qualification
is claimed. The existing 18 admission and six dependency-validator unit
scenarios remain unchanged.

Executable source:
[provider_metadata_admission_spec.spl](../../../../../test/02_integration/compiler/loader/provider_metadata_admission_spec.spl).

This manual serves provider and compiler authors investigating metadata
admission. Each setup creates a secure temporary directory beneath the current
working directory, opens the production CAS, and publishes runtime/std package
metadata with `runtime_std_publish_set_v1`. It reloads the runtime package with
`runtime_std_load_package_v1` and checks persisted identity and dependency
digests. These are real production callers of `package_image_validate_v1`.

For demand scenarios, `pinned_archive_open_verified_v1` opens and hashes the
actual persisted archive beneath its CAS root. Tests construct no fake open
capability and do not substitute an operating-system file handle. The positive
control reads `exports.smf` through the capability and checks its payload hash,
then calls `provider_admit_metadata_v1` twice and derives a production
`provider_execution_ticket_v1`.

Section payloads and build-action result records are metadata fixtures.
They do not prove compilation, executable SMF, dynamic loading, actual provider
effects, catalog registration, or discovery/loading of dependency providers.
The closure assertions concern exact metadata digest-list equality. The
REQ-005 assertions concern effect-owner policy and ticket identity only.

| Scenario | Action and expected observation | Requirement scope |
| --- | --- | --- |
| Valid dependency closure | Publish, reload, pin, read, admit twice; owner/observer flags differ while archive, receipt, dependencies, and ticket identity remain exact | REQ-002, REQ-012 |
| ABI error precedence | Change ABI, required dependencies, and shadow policy; all three demands return `abi_mismatch` | REQ-002, REQ-012 |
| Missing/malformed required ABI | Empty, short, and uppercase authority values return `abi_mismatch` | REQ-002, REQ-012 |
| Exact required dependency list | Empty, missing, extra, reordered, and substituted lists return `dependency_mismatch` | REQ-002, REQ-012 |
| Authenticated image dependency binding | Matching descriptor/caller lists that differ from the image return `dependency_mismatch` | REQ-002, REQ-012 |
| Package identity precedence | Package, ABI, and dependency disagreement returns `package_identity_mismatch` | REQ-002, REQ-012 |
| Closed real capability | Close before first demand and change package identity; `invalid_archive_capability` comes first | REQ-002, REQ-012 |
| Missing image sections | Remove sections and close the capability; `invalid_package_image` comes first | REQ-002, REQ-012 |
| Damaged receipt | Replace receipt digest and close capability; receipt validation fails and demand returns `invalid_package_image` | REQ-002, REQ-012 |
| Descriptor precedence | Empty requested dependency plus missing sections returns `invalid_descriptor` | REQ-002, REQ-012 |
| Published failure identity | Cause an actual ABI rejection, repair ABI, replace caller identity; repeated calls retain the original error and published provider/package/archive identity | REQ-002, REQ-012 |
| Shadow metadata positive control | Valid shadow mode retains primary effect owner on the execution ticket | REQ-002, REQ-005 |
| Policy rejection | Valid archive/ABI/closure reaches invalid direct-mode shadow policy; all demands return `invalid_dual_mode_policy` | REQ-002, REQ-005, REQ-012 |
| Malformed dependency publication | Empty, short, uppercase, and nonhex values cause `runtime-std-publication-invalid`; CURRENT and reloaded receipt/dependencies remain those of the valid generation | REQ-002, REQ-012 |
| Missing persisted receipt | Delete only the runtime receipt blob; reload returns `runtime-std-receipt-missing` with no image/receipt, while the standard package remains loadable | REQ-002, REQ-012 |
| Malformed persisted dependency | Rehash and store malformed dependency metadata through generic CAS publication; runtime reload returns `runtime-std-image-invalid` with no image/receipt, while the inherited standard package remains loadable | REQ-002, REQ-012 |
| Leaf positive control | Publish/reload/open/admit an empty dependency list successfully | REQ-002 |

The replay checker makes three real demand calls. On each it checks the exact
typed refusal, rejected terminal state, absence of a success receipt, and
published provider/package/archive identity. The separate mutation scenario
compares against the original published failure rather than later request
fields. Capability cleanup uses the owning close operation; temporary-store
cleanup is limited to the exact securely created directory.

The two persisted-read scenarios extend the original 15-scenario candidate
`bbbfb8a77ca2446bcde48210d7bd53d10b02f73f`. They exercise failures at the
production runtime package loader, rather than relying solely on the publisher
to reject new metadata. The generic CAS transaction used for the malformed
receipt is intentionally a lower-level writer: its correct hash proves stored
byte identity, not dependency validity. No new metadata policy is introduced.

Before qualification, execute this spec with the admitted self-hosted full CLI
on a POSIX host implementing the pinned-file owner, then regenerate this manual
with `spipe-docgen <spec> --output doc/06_spec --no-index`. Inspect generated
steps/captures and require zero stubs. Do not substitute the Rust seed. The
current Windows `runtime_file_view.c` owner explicitly returns unsupported
platform identity for pinned opens; the Windows HIR crash is an additional,
separate tooling blocker. Unsupported archive opening must fail setup, not
produce a skipped success.

No additional production change was inferred merely from writing these tests.
The already committed replay and dependency-format fixes remain the production
candidate. Source inspection predicts the pre-fix replay would return
`cached_rejection`, and the pre-fix publisher could admit malformed dependency
metadata; those are unexecuted regression expectations, not measured RED runs.
The incomplete loader adapter facade is deliberately not used as integration
evidence. Full unavailable-capability error parity remains outside this proof.
