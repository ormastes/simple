# SOSIX/QEMU External-Host Admission and Collector Gaps

**Date:** 2026-08-11  
**Status:** PARTIALLY RESOLVED  
**Acceptance criteria:** AC-3, AC-7, AC-8, AC-14

## Observed gaps

- A native Windows six-guest PowerShell wrapper now exists, but has only static
  Linux-host review because PowerShell and a Windows host are unavailable here.
- Unix host admission now proves accelerator advertisement and bounded QMP
  execution. Windows still records WHPX availability as unverified until its
  native wrapper gains an equivalent executable probe.
- Unix `--host windows|macos` relabeling and non-Windows execution of the
  PowerShell wrapper are rejected before PASS evidence can be created.
- A production collector now imports exactly 24 real bundles with owner,
  reviewer, resume, source, compiler, nonce, argv, and artifact identities.
- No current Windows SOSIX matrix artifacts or Windows VM assets exist under
  this host's configured storage. Six explicit macOS `blocked` receipts now
  live under `native-bundles/macos`; none claims native execution.
- External hosts default to `~/.simple`; the shared guide now documents the
  hash-preserving collector import into this host's `/mnt/data/.simple`.

## Unblock conditions

Execute and validate the PowerShell wrapper and WHPX probe on Windows, then
replace the retained macOS postponement rows with native admission/execution
receipts. Never promote Linux relabeling, TCG, or historical GPU reports.

- Owner: SOSIX/QEMU external-host integration lane
- Final reviewer: independent normal/highest-capability reviewer
