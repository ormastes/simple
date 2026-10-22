<!-- codex-architecture -->
# Simple Container cross-host architecture TLDR

Proposed design, 2026-09-26. Privilege selection and native host qualification remain pending.

- Common `RuntimeIdentityV1`/`RuntimeOperationV1` envelopes and pure host admission stay in `src/lib/common/contracts/container/`; providers own native execution and mutable lifecycle state.
- Linux targets rootless OCI execution. Windows Server targets native Windows process isolation. FreeBSD targets jail-backed native containers; its documented Podman route requires root and needs an explicit privilege decision. macOS only verifies fixtures in this lane.
- Exact host, guest and isolation matching prevents a VM or foreign guest from silently satisfying a native-container request.
- `require_unprivileged_client` means no administrator action per run. Authorized delegated clients can satisfy it. Strict rootless policy excludes delegation; zero-admin-ever additionally excludes `admin_setup: true`.
- SDN receipts describe observations and grant no authority. Only a live provider owner can authorize and commit a workload operation. Preflight PASS never proves native lifecycle support.
- SimpleOS shares result values through its real managed scheduler launch/exit seam; logs and durable recovery remain unavailable.
- Provider owners accept bounded child results after validating attempt/generation/native identity. Kernel enforcement remains MDSOC-only; existing SimpleOS userland ECS stays local.
- Probe on explicit preflight/session initialization. Cache static runtime metadata with executable/configuration invalidation. Revalidate authority after reconnect, user/boot/generation changes and identity before mutation. No full-container scans in request paths.
- Measure warm probe/lifecycle latency and RSS on native fixtures; numeric thresholds require selection before compliance claims.

Read [full architecture](simple_container_cross_host.md), [detail design](../05_design/simple_container_cross_host.md), and [test plan](../03_plan/sys_test/simple_container_cross_host.md). Root owns merge and Astra reviews executable evidence.
