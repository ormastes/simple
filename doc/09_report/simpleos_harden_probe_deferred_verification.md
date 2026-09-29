# Hardening probe deferred verification

Astra source review accepts the boot-media binding follow-up `4ba58f0ddfe`:
the launch checks kernel, embedded EFI image and firmware hashes, rejects
stale/duplicate receipt content and preserves the selected OVMF provider.
The selector/refusal regression and mutation fixtures exercise real paths.
Hashing runs once during admission; no guest hot path or retained allocation is
added. This is source acceptance, not a completed guest verification.

TODO (SimpleOS QEMU owner, after Linux bootstrap and admitted target compiler):
build with `sh scripts/check/build-simpleos-nvfs-positioned-qemu.shs --harden-probe`
using the required runtime/provenance/receipt environment, then run
`test/03_system/os/qemu/os/harden/cap_exec_gate_spec.spl` with the admitted
self-hosted test runner. Preserve boot-media hashes, fresh nonce output and
capability denial/allowed-exec evidence; record launch time and peak RSS.
Run `sh scripts/check/check-simpleos-harden-probe-build-target.shs` if this
revision lacks a retained successful selector/refusal receipt. Keep the bug OPEN.
