# Distributed build: local evidence and parallel handoff

**Status:** Prepared for separate owners; no live distributed-build or N2 performance PASS.
**Merge owner:** Primary distributed-build agent. **Final reviewer:** Astra or an equivalent highest-capability reviewer after executable evidence exists.

For a clean Linux checkout on the next host, run `sh scripts/check/check-dist-build-host-handoff.shs` on each worker before candidate build. Its `PREFLIGHT_ONLY` result is a prerequisite, not live qualification. The exact continuation checklist is [TODO 344](../../08_tracking/todo/dist_build_other_host_qualification_2026-09-26.md).

## Local observation on 2026-09-26

- Host is Darwin arm64. Docker client is 29.2.1; `podman` was not found on `PATH`.
- Docker context is `orbstack`. Its Unix socket exists at `/Users/ormastes/.orbstack/run/docker.sock` and is owned by the local user, but `docker info` from this managed workspace returned `permission denied` opening that socket. A separate local `orb status` reported `Stopped` (exit 1). A host-side owner must start OrbStack if appropriate and then probe the daemon anew; neither socket existence nor this sandbox's Docker error proves a working daemon.
- A fresh `orb start` attempt on 2026-09-26 stayed live for roughly 90 seconds without output while `orb status` still said `Stopped`; it was interrupted (exit 130). Do not restart it in a polling loop. A host-side GUI/service owner must diagnose startup before the Docker fixture can run.
- A macOS-hosted Linux guest may run a fixed fixture, but it cannot establish native Linux host isolation. The prior guest cgroup check found a read-only cgroup mount; repeat capability checks on the eventual worker rather than inheriting that observation.
- The self-hosted Simple verification runner previously exited 139; the session's three-cycle verification cap is exhausted. `bin/simple` currently resolves to `src/compiler_rust/target/bootstrap/simple`, while the separate pure-Simple release binary dates to 2026-07-25 and is not source matched. A focused test on `bin/simple` dropped its child before any assertion. New source and specs remain unrun. Do not turn seed or source-only checks into production PASS.
- Recent macOS crash reports identify a test-runner monitor `rt_process_spawn_async` fault rather than proven memory exhaustion. A Simple-only source mitigation now uses the existing shell facade for that one macOS monitor launch in both test-runner trees. A direct shell form returned a PID; the modified Simple path still requires a source-matched runtime and a fresh, bounded qualification session.
- The underlying macOS native spawn implementations were changed to `posix_spawnp` with bounded argument validation. A focused C self-check passed against both core and legacy runtime variants. This does not qualify the Simple FFI call path or reopen this session's exhausted distributed-build verification cap.
- The workflow, hook, and Linux OCI provider paths are dirty work in other lanes. Claim those files from their owners before editing or integrating them.

## Parallel lanes and evidence

| Lane | Exclusive work | Evidence required before merge |
|---|---|---|
| Local container fixture | A host-capable runner owns the Docker/OrbStack probe and fixed attach fixture. Keep it outside the OCI provider and hook files until ownership is agreed. | Record daemon identity and API version, exact full container ID, `tty=false`, attach before first start, framed raw stdout/stderr bytes, fixture count/digest, timeout, destroy and fresh exact-ID absence. Mark output completeness limited to the fixed fixture. |
| Linux isolation | A Linux runtime owner provides two scoped workers with delegated writable cgroup v2, pinned engine/image/worker digests, separate result-writer authority and authenticated transport. Small C operations stay in the owning runtime ABI; policy and scheduler stay in Simple. | Fresh per-ticket cgroup leaf, child attached before execution, bounded resources, kill/reap, `populated=0`, durable cleanup, worker-only result publication, wrong-identity and failure cases. No leader-only downgrade. |
| Verifier/coordinator | The scheduler owner joins the existing artifact snapshot and untrusted result reader to exact-ID OCI lifecycle and current-fence ledger. Coordinate provider-file ownership first. | Real two-node producer/consumer, staged executable, exact result bytes, terminal wait, destroy/absence, reboot/replay and stale-fence rejection. The current verifier's `BLOCKED` return remains until all evidence exists. |
| N2 and GitHub | A performance owner builds named staged-hook, one-ref pre-push and warm-preflight fixtures. The hook/CI owner qualifies signed local evidence under base-owned GitHub code, retaining required reporting and remote fallback. | Raw samples and mandatory gate receipts for N2 P95 ≤5 s, <10 s, <60 s; exact candidate/artifact/signature scope, signer revocation and base-drift negative cases; no skipped required check. Coordinate dirty hook/workflow ownership. |

The existing [agent breakdown](dist_build_scheduler_2026-09-25.md), [system test plan](../sys_test/dist_build_scheduler.md), [selected NFR](../../02_requirements/nfr/dist_build_scheduler.md), and [verifier blocker](../../08_tracking/bug/dist_exec_verifier_byte_capture_2026-09-26.md) remain the acceptance sources. Do not publish, release or claim host portability from discovery alone.
