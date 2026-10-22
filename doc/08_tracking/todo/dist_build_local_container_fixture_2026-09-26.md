# Distributed build: local container fixture qualification

Status: BLOCKED

The Darwin arm64 host has Docker 29.2.1 configured for OrbStack, but the managed workspace cannot open its Unix socket (`docker info` returned `permission denied`). A separate local `orb status` reported `Stopped` (exit 1). An agent with host-side access must start OrbStack if appropriate, establish fresh daemon state, and run the fixed binary-output fixture. Socket file existence does not prove connectivity.

On 2026-09-26, `orb start` stayed live without output for roughly 90 seconds,
`orb status` remained `Stopped`, and the start was interrupted (exit 130). The
same in-sandbox start should not be retried without new startup evidence.

On 2026-09-27, OrbStack still reported `Stopped`. Read-only probes of both
`desktop-linux` and `default` Docker contexts returned Unix-socket permission
denied. `orbctl doctor` found that `/usr/local/bin/docker` resolves to Docker
Desktop rather than OrbStack and reported CLI/plugin path conflicts. No host
symlinks or Docker configuration were changed. A host-side owner should fix
the daemon/access path and pin the intended context before the fixture runs;
these diagnostics do not authorize a container PASS.

Acceptance: retain the daemon/API identity, a full exact container ID, never-started and `tty=false` evidence, attach with `logs=0` before start, bounded framed stdout/stderr bytes, independent expected count and SHA-256, and terminal destroy followed by fresh exact-ID absence. Record timeouts and negative cases. This can qualify only the deterministic fixture's observed bytes; it cannot prove arbitrary program output completeness or native Linux isolation.

Owner handoff: [distributed-build local handoff](../../03_plan/agent_tasks/dist_build_local_handoff_2026-09-26.md). Do not change the other lane's dirty OCI provider file without an ownership transfer.
