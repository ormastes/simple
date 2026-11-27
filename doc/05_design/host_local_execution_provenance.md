# Host local execution provenance

The isolated branch starts from release commit
`862d9e361534c1a13f83a2f43da06e07847df5af`. Shared-main source was read only.
The following two narrow pre-existing files were untracked in shared main at
`671d5545201c5c5bc73ea0ddaf0db0f143218d44`; that commit is workspace context,
not a claim that it contains these blobs. This branch records their admission.

| Existing source | Original SHA-256 | Admission change |
|---|---|---|
| `src/lib/common/contracts/orchestration/host_prepare_request_v1.spl` | `7891892b2425cf3efc56dfb52a0ecd753c78a199e5d042a76a5aa28bf2c2217a` | Enforce packet bounds with byte length, preserving wire format |
| `src/lib/nogc_sync_mut/orchestration/host_authorized_reservation_v1.spl` | `3c9caa305d011307581921abc7feef320ced4f855c68df543d34cd0294951aad` | Existing signed authority and owner-return reply composition |

The old main-only Linux launch/store code was inspected as design evidence.
The final common Container execution consumer does not import its unrelated
cleanup/storage-observation dependencies. Existing committed journal, authority,
HostConfig, reservation and enrollment foundations retain their original owners.

New core, root composition, intent/observation retention, tests and manuals are
host-owned. Shared Container contracts/factory are orchestrator-owned; native
Linux and Windows adapters remain with their provider leads. App command routing
is orchestrator-owned. Runtime qualification is NOT_RUN.
