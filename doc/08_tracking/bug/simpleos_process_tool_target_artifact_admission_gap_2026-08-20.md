# SimpleOS process tool target artifact admission gap
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — release blocker
**Owner:** process-tool package, launcher, loader, and target-build owners
**Found:** 2026-08-20

## Current state

The canonical process-monitoring implementation reads the bounded kernel task
snapshot through `os.userlib.process`, and `/usr/bin/ps` has an exact artifact,
package, and launcher contract. Shell direct, alias, background, pipeline, and
`which` paths cannot use the old in-process builtin or PATH fallback.

The package has no target-native bytes, digest, or loader-owned admission token.
The launcher therefore returns exit 126 with
`PROCESS_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE`, and the primary-tool manifest
truthfully keeps the process row `Blocked`.

## Required closure evidence

- Build and stage exact `/usr/bin/ps` artifacts for x86_64, AArch64, and RV64.
- Bind artifact digests and loader authority without a public mint seam.
- Execute help, version, normal listing, filter, malformed-option, and task-list
  failure behavior from FAT32, DBFS, and NVFS.
- Retain target/runtime receipts and representative latency/RSS evidence.


## Round-10 verdict note (2026-11-06)
RELEASE BLOCKER reviewed in depth. Verdict: host-blocked (not closable by code in this lane). src/os/services/launcher/launcher_process_tool_gate.spl is correctly fail-closed: it returns PROCESS_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE because the package digest and receipt id name no real bytes. Closure needs (1) target-native /usr/bin/ps for x86_64, AArch64 and RV64 built by the image pipeline, (2) independently computed digests bound by a loader-owned token with no public mint seam, (3) help/version/list/filter/malformed/task-list-failure runs from FAT32, DBFS and NVFS under real-firmware QEMU plus the board path (board-runnable rule), (4) latency/RSS receipts. Minting a token or flipping the manifest row from Blocked without those bytes would fake admission. The blocked contract is pinned by test/01_unit/os/process_tool_artifact_contract_spec.spl. Owner decision: ship with ps Blocked and documented, or hold for the QEMU artifact lane.
