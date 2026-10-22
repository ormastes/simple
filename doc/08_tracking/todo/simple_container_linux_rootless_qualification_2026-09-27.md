# Qualify the Linux rootless Simple Container provider

Status: BLOCKED. Priority: P1. Owner: Linux container integration.

The shared host capability contract and Linux Podman probe adapter exist in
`src/lib/common/contracts/container/host_capability_v1.spl` and
`src/lib/nogc_async_mut/container/providers/linux/host_capability_v1.spl`.
The adapter reports discovery only; it does not prove a managed workload ran.
The current macOS host cannot qualify Linux user namespaces, delegated cgroups,
or the Linux OCI lifecycle.

On a clean Linux host, select the unprivileged client policy from
`doc/02_requirements/feature/simple_container_cross_host_options.md` before
claiming support. Use a non-root caller and a live rootless Podman provider.
Record the provider, host and guest OS, image digest, namespace mapping,
delegated cgroup behavior, and an SDN capability receipt. Exercise real
create, start, wait, stop, and destroy operations through the common
`RuntimeIdentityV1` and `RuntimeOperationV1` contract. Retain the exact task
exit and fresh absence evidence after destroy. Reject a scripted probe,
root caller, stale identity, unsupported image, missing delegation, timeout,
and failed cleanup. Run the focused Simple specs with a source-matched
self-hosted runtime and retain its provenance.

Acceptance: a non-root Linux client launches one isolated workload, receives
its real exit, and destroys it without an administrator prompt; negative cases
fail closed and leave no managed resource. A probe-only receipt is insufficient.
Keep this TODO open until the live Linux fixture and executable specs pass.

Related: [cross-host qualification](simple_container_cross_host_qualification_2026-09-26.md).
