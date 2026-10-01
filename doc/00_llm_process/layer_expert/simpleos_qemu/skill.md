# Layer Expert: SimpleOS QEMU Evidence Ownership

## Boundary

This layer owns host settings/admission, per-run media isolation, QEMU row
execution, evidence production, and parent-authoritative matrix collection. It
does not own guest compiler lowering or architecture privilege-entry internals.

## Canonical ownership

- `scripts/qemu/simple-qemu-settings.shs`: shared host/storage mapping.
- `scripts/qemu/simple-qemu-host-admission.shs`: actual host, QEMU, accelerator, and hash identity.
- `scripts/os/prepare_qemu_nonce_media.shs`: row-owned copied media and nonce readback.
- `scripts/check/produce-sosix-qemu-native-pass-bundle.shs`: child/row result envelope.
- `scripts/check/collect-sosix-qemu-evidence.shs`: sole parent commit for 24 rows.

Boundary data is copied media or an encoded/hash-bound evidence payload; raw
pointers and shared writable base images never cross a row boundary. The row
creates its result, `/root` validates/merges it, and the collector commits in a
deterministic 24-row order.

## References and update rule

Follow the [canonical plan](../../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md),
[operator guide](../../../07_guide/platform/simpleos/sosix_qemu_shared_settings.md),
and [open-owner record](../../../08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md).
Update all three plus the evidence ledger whenever an interface, row state,
ownership rule, or host-unavailable contract changes.

## Default CLI sealed dispatch

The default non-debug CLI source route uses `run_os_sealed_v1` and
`os.qemu_cli_plan_v1.qemu_cli_dispatch_plan_v1`; inspection and execution retain
one sealed plan. Keep artifact guards before dispatch and do not reconstruct
argv from display text. Named/GUI migration remains open. This change is
TEST_BLOCKED pending self-hosted runtime/docgen/CLI qualification; see
`doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md` and the matching feature
expert `simpleos_sealed_cli_dispatch`. It provides no matrix or release PASS.
