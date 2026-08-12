<!-- codex-architecture -->
# SOSIX QEMU direct-kernel evidence schema v2

## Status

Proposed for root/high-capability review. No matrix row is promoted by this
change and a fresh pre-admitted run is mandatory after acceptance.

## Context

The v1 native PASS schema assumes an external UEFI, OpenSBI, or board-ROM
artifact. QEMU RV32 can instead use `-bios none` and load the kernel directly.
Representing that mode as a fabricated firmware file or OpenSBI handoff would
make the evidence false.

## Decision

Schema v2 adds one closed mode:

- `firmware_identity=firmware:none`
- `firmware_mode=direct-kernel`
- `firmware_path=none`
- `firmware_version=version:none`
- `firmware_sha256=none`
- `firmware_stage_markers=guest-entry`

`guest-entry` is a literal, ordered transcript event distinct from the run
nonce and workload markers. Direct-kernel bundles contain eight artifacts and
omit `firmware.bin`; all external-firmware modes still require nine artifacts
and hash-bound firmware bytes. The producer continues to require the closed
pre-run host admission record. The collector accepts v1 for existing external
firmware rows and v2 for all modes, but direct-kernel is v2-only.

The collector remains the sole matrix admission owner. Producer evidence does
not itself promote a row.

## Invariants

- A nonce identifies one immutable workload run and cannot double as
  `guest-entry`.
- `direct-kernel` never accepts a firmware path, version, or digest other than
  the exact `none` sentinels.
- UEFI/OpenSBI/board-ROM never accept absent firmware bytes.
- Hash-selected argv, kernel, image, program, and transcript artifacts remain
  unique and immutable.
- A fresh run must be admitted before launch; post-hoc admission is invalid.

## Review ownership

Lower-model sidecar: `N/A` (Codex Spark unavailable). Merge owner: root agent.
Final reviewer: root/high-capability model.

