<!-- codex-research -->

# SimpleOS Enhancement — Domain Research

## Decision-relevant findings

### Capability enforcement

seL4 defines a capability as an unforgeable permission to a kernel object and
initializes the root task with capabilities to the objects it must manage.
Fuchsia separately associates rights with handles and allows those rights to be
reduced on duplication or replacement. Together these support the selected
SimpleOS direction: bootstrap receives a distinguished root mint object, while
ordinary workloads receive explicit, attenuable, generation-checked handles.
An empty capability space must mean no authority, not ambient full authority.

### Workload identity

SPIFFE's workload identity material is designed to be issued through a workload
API and rotated. SimpleOS should use a short-lived, process-bound identity for
authenticated IPC and networking, but retain runtime authorization in object
capabilities and broker policy. Identity therefore authenticates a principal;
it does not become a bearer bundle of permanent privileges.

### Service supervision

systemd demonstrates the needed production responsibilities: dependency order,
readiness, health/watchdog behavior, bounded restart, rate limiting, and
orderly shutdown. SimpleOS must retain its capability-specific rule: a restart
is a new workload instance, so the old CSpace and all delegated grants are
revoked before policy reacquires fresh grants.

### Isolation and containers

The OCI runtime specification models a workload as a root filesystem plus
namespaces, process limits, devices, resource controls, and lifecycle setup.
SimpleOS need not copy Linux namespace internals, but an isolation domain must
provide equivalent observable boundaries for filesystem, PID/process, IPC,
network, devices, and resources. gVisor's application-kernel approach confirms
that a stronger sandbox is a separate tier, appropriate where native
process/container isolation still shares too much of the host kernel.

### Restriction layers

Linux seccomp documentation is explicit that syscall filtering is not a
complete sandbox. In SimpleOS, syscall filters are therefore only an
additional monotonic restriction: object-handle authorization remains the
authoritative allow decision.

## Architecture implications

1. Compile human, service, agent, and container policy to one workload policy
   and one spawn path; roles never appear as kernel authorization strings.
2. Construct an immutable `KernelCallContext` at syscall dispatch and pass it
   to every security-sensitive downstream path.
3. Represent process, directory, endpoint, network, secret, model, and tool
   authority as typed, rights-reduced, generation-checked handles.
4. Bind every task to a job, CSpace, isolation domain, resource domain, and
   audit identity, with child budgets/authority bounded by the parent.
5. Make native containers a composition of these primitives and reserve a
   separate strong-sandbox tier for hostile native code.

## Sources

- [seL4 capabilities](https://docs.sel4.systems/Tutorials/capabilities.html)
- [Fuchsia handle rights](https://fuchsia.dev/fuchsia-src/concepts/kernel/rights)
- [SPIFFE SVID deployment](https://spiffe.io/docs/latest/deploying/svids/)
- [Linux seccomp filter documentation](https://www.kernel.org/doc/html/v5.9/userspace-api/seccomp_filter.html)
- [OCI Linux runtime configuration](https://github.com/opencontainers/runtime-spec/blob/main/config-linux.md)
- [gVisor overview](https://gvisor.dev/docs/)
- [systemd overview](https://wiki.freedesktop.org/www/Software/systemd/)
