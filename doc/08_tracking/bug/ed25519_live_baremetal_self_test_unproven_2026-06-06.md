# Ed25519 Live Baremetal Self-Test Fails Or Remains Unproven In SSHD QEMU Lane

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; the previously-picked repro spec did not clearly correspond to this record's own defect, so it was not trusted, and no cheaper repro is available within budget; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Remediation 2026-09-12: an earlier automated pass matched a spec path mentioned in this record and ran it, but on review that spec was not clearly this record's own reproduction (see evidence); the RESOLVED/still-reproduces verdict was withdrawn and the record was re-closed stale by age instead, without re-running an unverified repro. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
