# Seatbelt: failed-control probe could qualify; broker socket path unbounded (2026-11-14)

Found re-qualifying the direct-Seatbelt lane on macOS 26.5 (25F71) arm64. Both fixed.

## 1. Decoder ignored the probe's unconfined control (fail-open)

`seatbelt_manifest_from_probe_v1`
(`src/lib/nogc_async_mut/container/providers/macos/seatbelt_capabilities_v1.spl`)
read only `canary ...` lines. `sosix_darwin_sandbox_v1_selfcheck.c` prints all 23
canary lines even when `control unconfined-reachability FAIL` (e.g. offline host:
DNS "denied" without any sandbox), then exits 1. Feeding that stdout to the
decoder produced a QUALIFIED manifest from a failed probe.

Fix: the transcript must contain `control unconfined-reachability ok`; a failed or
missing control, or any `FAIL` line, rejects the transcript.

## 2. Broker socket path could exceed Darwin `sun_path` (103 bytes)

`seatbelt_attempt_dir_plan_v1` (`.../macos/seatbelt_provider_v1.spl`) accepted any
`state_root` (<= 1024) plus attempt key (<= 128), so
`<root>/attempts/<key>/ipc/broker.sock` could be unbindable; the profile would
still be compiled for it. The probe itself `strncpy`-truncated the path and bound
a different socket (observed: `other: Address already in use`).

Fix: the plan refuses a broker socket path > 103 bytes
(`SCMAC-FS-002 broker_socket path-exceeds-darwin-sun-path`) before any effect;
the probe exits 2 instead of truncating.

## Specs

- `test/01_unit/lib/nogc_async_mut/container/providers/macos/seatbelt_capabilities_v1_spec.spl`
  — "refuses a transcript whose unconfined control failed or is absent"
  (reproducer: control FAIL; generalization: missing control, `FAIL` line).
- `test/01_unit/lib/nogc_async_mut/container/providers/macos/seatbelt_provider_v1_spec.spl`
  — "refuses a broker socket path that Darwin sun_path cannot hold"
  (reproducer: long key at the 103/104 boundary; generalization: long state root).

## Evidence

Native probe rebuilt from this change: 23/23 canaries, control ok; real
transcript decodes to `qualified`. BSD: Darwin-only code paths, no FreeBSD change.
