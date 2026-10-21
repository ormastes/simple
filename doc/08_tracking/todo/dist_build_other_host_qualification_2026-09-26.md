# Distributed build: continue qualification on another host

Status: BLOCKED on a clean Linux checkout with two scoped workers and a source-matched admitted Stage 4 compiler.

Run `sh scripts/check/check-dist-build-host-handoff.shs` for a Docker worker,
or `sh scripts/check/check-dist-build-rootless-podman-host.shs` for a local
rootless Podman worker, on each proposed Linux host. Keep the bounded output
with host identity and source commit. `PREFLIGHT_ONLY` is a prerequisite
receipt, not a distributed-build PASS. A blocked preflight must be fixed
before running a worker.

The Podman preflight records a non-root caller, local Podman engine, cgroup v2
configuration, and actual subordinate UID/GID maps in bounded SDN. Podman is
daemonless; `podman info` is an engine check, not proof of a service daemon.
The script labels cgroup delegation `live-fixture-required` because engine
metadata and namespace maps do not prove enforcement or exact-ID cleanup.
Run the same native lifecycle fixture next. A Podman-only host is not rejected
solely because Docker is absent. [Podman info fields](https://docs.podman.io/en/latest/markdown/podman-info.1.html)
and [rootless mode](https://docs.podman.io/en/stable/markdown/podman.1.html)
document these prerequisites.

Once the distributed-build source drafts are committed and available on that host, run `sh scripts/check/check-dist-issued-native.shs <Stage-4-binary> <adjacent-Stage-4-provenance>` from a clean checkout to build private native candidates. Preserve the resulting hashes, logs, and `CANDIDATE_BUILT_UNQUALIFIED` receipt. Do not substitute the Rust seed or an older release binary.

Then complete TODO 338 (fixed Docker attach bytes and exact-ID destroy), TODO 339 (two delegated cgroup v2 Linux workers and live staged build), TODO 340 (raw N2 samples), TODO 341 (signed CI with required reporting), TODO 342 (macOS SimpleOS guest route), and TODO 343 (macOS runner crash source-path qualification). Use the [distributed-build handoff](../../03_plan/agent_tasks/dist_build_local_handoff_2026-09-26.md) for exact evidence and lane ownership. The other host must claim workflow, hook, and OCI provider files from their current owners before editing.

Acceptance: a source-matched self-hosted runner passes the relevant Simple specs and smoke checks; the live two-node worker and failure/replay evidence pass; N2 receipts meet their selected thresholds; required GitHub checks still report; verification reaches `STATUS: PASS`. Until then, keep the distributed-build verifier blocked and do not publish a release.
