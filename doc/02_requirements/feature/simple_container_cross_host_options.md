<!-- codex-research -->
# Simple Container cross-host feature options (selection pending)

Fixed in `doc/03_plan/agent_tasks/simple_container_cross_host_parallel_2026-09-26.md`: pure `ContainerHostCapabilityV1` admission, exact native host/execution-OS/isolation match, SDN capability receipt, and provider-owned lifecycle. The user selected native macOS, SimpleOS, and Windows process execution; VM routes are excluded. These options select the **client privilege policy** for live host leaves. No option is selected here.

| Option | Description | Pros | Cons | Effort |
|---|---|---|---|---|
| F1 — strict non-root client | Admit Linux rootless Podman. Report Windows/FreeBSD native launch unavailable until a non-root route is proven. Mac uses native App Sandbox when qualified. | Smallest authority surface; immediate truthful Linux slice. | No live Windows/FreeBSD launch in this phase. | M, about 4–7 new files plus host fixtures. |
| F2 — scoped delegated launch | Keep ordinary Simple clients non-admin; introduce a separately owned, authenticated, operation-scoped broker for Windows HCS and FreeBSD jail/Podman. `delegated` becomes launch-capable only after broker proof. | Enables real Windows/FreeBSD containers while limiting client authority; aligns with fixed capability schema. | Broker security, authorization, audit, and recovery are substantial; root/admin still exists in the broker. | XL, about 15–25 files plus host integration fixtures. |
| F3 — operator-run privileged provider | Permit explicit Administrator/root execution on dedicated qualified Windows/FreeBSD hosts; label the client as privileged through a revised capability vocabulary before implementation. Linux remains rootless where qualified. | Fastest live Windows/FreeBSD prototype. | Broad operator authority and weaker separation; fixed `client_privilege` values lack a direct privileged-client state, so contract revision is required. | L, about 10–16 files plus host fixtures and contract update. |

Each option requires Windows process isolation only, FreeBSD root requirement disclosure, no automatic VM downgrade, and native exit/cleanup evidence. The SimpleOS kernel provider is a separate native backend; the former guest adapter is superseded.
