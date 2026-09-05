# SimpleOS process tool target artifact admission gap

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
