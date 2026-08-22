# Trusted HAL provider launcher evidence — 2026-08-22

## Scope

The launcher is an initialization/compatibility boundary for the Pure Simple,
C, and Rust provider lanes. The coordinator pins it and all three providers to
root-installed `/usr/libexec/simple/*-v1` identities. Provider images are
opened with `O_PATH|O_NOFOLLOW`, validated as root-owned/non-writable ELF
executables, and passed by preserved descriptor to avoid pathname replacement.

The worker receives only bounded stdin/stdout protocol endpoints. The launcher
clears the environment, exhaustively closes ambient descriptors with
`close_range`, applies `no_new_privs` and parent-death supervision, and enters
Bubblewrap with fresh user/PID/network/IPC/UTS/mount namespaces, a minimal
read-only `/usr`/library root, private `/tmp`, and no host `/run`, home, or
secret mounts. Fixed RLIMITs bound address space, processes, CPU, file output,
descriptors, and core output. Deadline cancellation kills the process group and
reaps the direct namespace supervisor; Bubblewrap `--die-with-parent` owns its
descendants.

## Evidence

- `scripts/check/check-hal-provider-launcher-v1.shs`: PASS. This host cannot
  create the required namespaces, and the launcher returned no isolation or
  provider receipt. This proves the local fail-closed branch, not successful
  sandbox admission.
- `scripts/check/check-hal-provider-launcher-v1-perf.shs`: UNVERIFIED (exit 2).
  Namespace creation is unavailable, so admitted launch latency and max RSS
  cannot be measured on this host. The 512-byte result cap and fixed stack
  buffers are source-enforced; no direct heap API is present, but this is not a
  dynamic allocation proof.
- `bin/release/simple check src/app/hal_provider`: BLOCKED before compilation
  because the deployed self-hosted runtime failed its bounded identity probe.
  No Rust-seed fallback was used.

## Critical-mode disposition

The current coordinator spawns per invocation. It therefore forcibly revokes
commit for Critical and Verified operations even when comparison/isolation
receipts are otherwise valid. `critical_ready` remains false. Production
critical admission requires a separately verified, preinitialized provider
session owner sealed before the no-allocation epoch plus successful namespace,
latency, RSS, and allocation evidence on a capable host.
