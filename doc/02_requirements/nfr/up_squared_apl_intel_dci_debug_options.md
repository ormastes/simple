# NFR options: UP Squared Apollo Lake Intel DCI debug

Date: 2026-08-21

No option is selected yet. The baseline below is recommended for every feature
option; stricter alternatives may be selected independently.

## Safety baseline (recommended)

- Fail closed unless exact board/FAB, firmware, cable, debugger, and target
  connection receipt are present.
- Never flash BIOS, write MSRs, or mutate persistent storage by default.
- Reject Apollo Lake OpenRC warm reset; recovery defaults to a physical reset.
- Admit only hash-bound payloads and allowlisted RAM ranges from a current map.
- Storage writes require stable identity, explicit confirmation, bounded write,
  flush, and exact-length readback hash.
- Use a physically controlled secret-free target and disable DCI after work.
- Pros: minimizes bricking, wrong-disk writes, and debug-security exposure.
- Cons: more setup and receipts; blocks convenient guesses.
- Effort: medium.

## Recovery-qualified firmware experimentation

Permit a separately authorized firmware/debug-consent lane only with exact FAB
matching, full SPI backup, external recovery programmer, and tested restore.

- Pros: may unlock DCI on production firmware that currently blocks it.
- Cons: real brick/security risk; old Intel FAB-A images may be incompatible.
- Effort: large.

## Evidence levels

- Contract PASS: checker and documentation are internally consistent.
- Connection PASS: Intel tool identifies the exact Apollo Lake target.
- Run-control PASS: retained halt/resume/reset and known-memory read evidence.
- Boot PASS: fresh UART markers and command-correlated VFS `ls /` evidence.
- Storage PASS: exact identity, write bounds, flush, and full readback hash.
- Pros: prevents offline or partial evidence being mislabeled as hardware PASS.
- Cons: requires retaining several receipts.
- Effort: small.
