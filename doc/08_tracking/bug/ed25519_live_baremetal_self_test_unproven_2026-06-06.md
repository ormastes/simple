# Ed25519 Live Baremetal Self-Test Fails Or Remains Unproven In SSHD QEMU Lane

Status: Open.

Date: 2026-06-06

## Status

Open.

## Summary

Pure Simple Ed25519 interpreter tests and the in-memory SSH production transcript pass,
but the live x86_64 baremetal SSHD lane has observed `Ed25519 self-test failed in live lane`.
The current live SSH gate therefore disables Ed25519 when embedded RSA host material is
available and drives the RSA host-key path first.

## Evidence

- Interpreter Ed25519/SSH transcript evidence remains green:
  - `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl`
  - `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl`
- Live entry policy:
  - `examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl`
- Daemon live startup guard:
  - `src/os/apps/sshd/sshd.spl`

## Required Fix

Add a dedicated baremetal Ed25519 KAT lane and only re-enable live Ed25519 advertisement
after the KAT passes in QEMU/baremetal, not only in interpreter mode.
