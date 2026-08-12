# SOSIX QEMU direct-kernel evidence v2 design

## Producer

`produce-sosix-qemu-native-pass-bundle.shs` validates mode/stage pairs before
reading artifacts. Direct-kernel requires `none` for all external firmware
arguments, copies no firmware artifact, emits schema v2, and declares eight
artifacts. External modes preserve their file check and nine-artifact bundle.

## Collector

`collect-sosix-qemu-evidence.shs` accepts schema 1 or 2. It rejects
direct-kernel under v1 and validates the exact no-firmware tuple under v2. The
ordered stage loop requires literal `guest-entry` in the hash-selected
transcript. Output manifests and collector-generated admission records are v2.

## Fresh-run protocol

1. Emit the closed host admission before QEMU starts.
2. Launch with the exact one-line argv containing `-bios none`.
3. Emit literal `guest-entry` on entry to the kernel, before the nonce.
4. Emit the unique nonce and real filesystem workload lifecycle.
5. Produce v2 evidence through the canonical producer.
6. Import only through the canonical 24-cell collector.

## Sabotage coverage

The focused producer test covers valid direct-kernel output and rejects absent
external firmware and fake guest entry. It proves argv/kernel tampering differs
from declared hashes. Collector source keeps duplicate-nonce rejection and
hash-selected artifact uniqueness gates; root review must require those gates
to remain intact before accepting the patch.

