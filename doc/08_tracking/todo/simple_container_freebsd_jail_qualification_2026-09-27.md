# Qualify the FreeBSD jail-backed Simple Container provider

Status: BLOCKED. Priority: P1. Owner: FreeBSD container integration.

The shared `ContainerHostCapabilityV1`, `RuntimeIdentityV1`, and
`RuntimeOperationV1` contracts exist, but there is no FreeBSD jail-backed
provider or live FreeBSD container fixture in this worktree. The separate
FreeBSD QEMU bootstrap TODO proves compiler and runtime qualification only;
it cannot prove jail lifecycle or isolation.

First select the client privilege and isolation requirements from
`doc/02_requirements/feature/simple_container_cross_host_options.md`.
Implement the OCI/Podman `ocijail` route with explicit root authority, or a
separately selected and scoped delegated service/VM route. A non-root client
calling a root-owned service is delegated, not rootless. Keep jail identifiers,
native mutable state, and authorization in the provider; do not promote a
capability receipt into launch authority. Record FreeBSD host release, guest
userland and immutable image digest, runtime version, storage/network setup,
caller identity, actual jail identity, and isolation mode in bounded SDN.

On a FreeBSD host, run the focused contract and native system specs with a
source-matched self-hosted Simple runtime. Check host/guest compatibility and
provisioned storage/network facilities before create. Exercise real create,
start, wait, stop, and destroy with a unique output marker and chosen nonzero
exit. Retain the exact jail and attempt identity, task exit, bounded output,
and fresh absence after destroy. Verify that an unmounted host sentinel is
unreadable and that denied jail privileges remain denied. Test an unauthorized
caller, wrong image/host tuple, stale attempt, timeout, failed create cleanup,
repeated destroy, and denial when required setup or authority is absent. If a
delegated route is selected, prove the broker's scope and the independent
administrative provisioning step.

Acceptance: the selected FreeBSD route runs an isolated workload in a real
jail, returns its native exit, enforces the recorded authority, and destroys
the bound jail. A successful FreeBSD bootstrap, jail command probe, or scripted
contract result alone cannot close this TODO.

Related: [cross-host qualification](simple_container_cross_host_qualification_2026-09-26.md)
and [system test plan](../../03_plan/sys_test/simple_container_cross_host.md).
