# Actual installed Linux fresh-epoch preparation

Source: `test/03_system/tools/linux_installed_fresh_epoch_v1_spec.spl`.
Status: AUTHORED_NOT_RUN. Manual authored alongside source; docgen, compiler,
link, native faults and Podman execution were not run. No pass/coverage claim.

Use a disposable already provisioned dedicated Host system unit matching the
34-field fixed fresh-epoch profile, machine and supervisor profiles. The main
Host must have the exact allowed inherited environment, actual root-controlled
finite cgroup2 parent/delegation/supervisor and protected empty graph/runtime
roots. ext4/XFS graph and ext4/XFS/tmpfs runtime are the supported first filesystems.
Provider/socket/user-manager persistent masks must already exist; provider and
socket units must be loaded, inactive, jobless and never started. The account is
nonroot/nologin with `/nonexistent` home and exact subordinate-ID ranges.
Provisioning is a prerequisite, never performed by this spec or this source task.

Run this spec only after a separately admitted native runtime/link qualification.
Missing or mismatched provisioning FAILS with the real error; it is not skipped
or converted into a passing unsupported case. Pending owners remain in explicit
fixture arrays for cleanup inspection. The spec creates no charge or launch.

1. **Open the fixed installed profiles inside the actual dedicated Host system unit.**
   Open genuine lower preparation and read actual native diagnostics. Verify
   nonzero UID/GID/generation, authenticated manager name, native identity digest
   shape and partition=usable+reserved arithmetic, with positive outside charge.
2. **Contend on the actual fixed machine-state epoch lock without another writer.**
   A second actual factory must fail specifically at lock acquisition, with
   complete cleanup. Original current must retain the same store identity.
3. **Transfer the same retained native owners; this transition creates no durable admission.**
   Consume preparation into the supporting successor. Every copied preparation
   alias must reject current; closing it must leave successor current valid.
4. **Close the actual successor once; copied aliases cannot revive preparation or a later lock.**
   Verify positive closure, no returned owner, current refusal and idempotent
   canonical close. No process or provider is created.
5. **Acquire real supported preparation before placing one uniquely owned fixture sentinel.**
   Reopen a real fresh preparation and independent genuine installed profile.
   Explicitly fail before mutation if profile digests differ. Exclusively create
   one generation-named test sentinel in the already verified graph root.
6. **Observe native nonemptiness refusal, remove only the fixture sentinel and preserve cleanup.**
   Current must report `fresh-epoch-native-store-nonempty`; remove only the
   exclusive test sentinel, verify absence, and require transition refusal even
   after removal because the original owner is now cleanup-only. Close owners.
7. **Read genuine installed bytes and vary data only; decoding creates no native custody.**
   Add an unknown callerSaysFresh field and an invalid reserved=partition budget
   independently. Both strict validations must refuse; close the genuine reader.

Traceability: REQ-LINUX-FRESH-EPOCH-001–004 have authored concrete scenarios;
005–006 additionally require independent source review and upper/native fixtures.
No branch coverage percentage is asserted. Native PID namespace/fork collision,
same-procfs bind mounts, manager/mask/credential/ACL changes, finite-limit pressure,
close fault injection, actual WAL CAS/crash/orphan repair and real Podman workload
ancestry/enforcement remain NOT_RUN / NOT_COVERED. No mock metadata receipt is
accepted as a substitute for those native assertions.

Separate actual negative fixtures (each requires its own administrator-prepared
state and is never run as a mutually incompatible combined fixture):

- [Subordinate UID occupant](linux_fresh_epoch_subuid_occupant_v1_spec.md).
- [Unknown partition occupant](linux_fresh_epoch_partition_occupant_v1_spec.md).
- [Pinned executable capability](linux_fresh_epoch_executable_capability_v1_spec.md).

All three are AUTHORED_NOT_RUN and require their exact production error branch;
a generic unsupported result is a failure, not evidence.
