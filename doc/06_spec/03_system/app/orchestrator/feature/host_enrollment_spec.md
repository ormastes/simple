# Signed host enrollment binding

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored manual, not generated execution evidence.

Implementation: `src/lib/nogc_sync_mut/orchestration/host_enrollment_v1.spl`.
Executable: `test/03_system/app/orchestrator/feature/host_enrollment_spec.spl`.
Real-signature fixture: `test/fixtures/orchestration/host_enrollment_native_probe.spl`.

| Requirement | Authored evidence |
| --- | --- |
| HOST-ENROLLMENT-01 | Canonical versioned SDN binding hashes all six fields; canonical bounded credential roundtrip delegates operation/grant/approval wire formats to existing codecs. Malformed, unknown, noncanonical, oversized UTF-8 source and invalid native identifiers/paths/digests reject. |
| HOST-ENROLLMENT-02 | Real Ed25519 issuer and separate approver signatures authorize the fixture's enrollment envelope. Each binding field, action, provider digest, expected host/memory, policy digest/context and approval clock are independently mutated and rejected. Corrupt signatures reject. Recomputing a changed payload digest still rejects old approval metadata; recomputing approval metadata without signing rejects its signature. |

Fixed payload kind: `host-enrollment-binding`; fields: `version`, `kind`, `configDigest`, `policyDigest`, `nativeMachineId`, `nativeBootId`, `providerIdentityDigest`, `machineParent`.
Fixed credential kind: `host-enrollment-credential`; fields: `version`, `kind`, `operation`, `signedGrant`, `signedApproval`. The last three values contain existing V2 wire strings.

The fixture reuses deterministic test keys/seeds from `test/fixtures/daemon_sdk/distributed_authority_verification_fixture_v2.spl`, signs the actual enrollment grant and envelope with the existing Ed25519 implementation, and verifies through the existing indexed authority snapshot verifier. No cryptographic implementation is duplicated.

This module performs no filesystem, provider or root-claim effects. Its input fields are data. The trusted consumer must acquire actual native observations, authenticate the locally provisioned policy, and claim the installed machine authority root separately. A canonical absolute parent path does not prove absence of symlinks, root ownership, physical-host uniqueness or boot/provider continuity. These tests cannot establish those consumer properties.

Compilation, SSpec execution, native observation/root claims and live host enrollment have not run for this source change. No admitted runtime or deployment qualification is claimed.
