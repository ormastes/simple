<!-- codex-research -->

# SimpleOS Enhancement Requirements

The user-selected direction is one live execution-security model: role and
manifest policy compile to object capabilities, while the kernel authorizes
only live, typed handles and an immutable caller context.

## Functional requirements

- REQ-001: Syscall dispatch constructs one immutable `KernelCallContext` with
  task, principal, job, CSpace, isolation, resource, and audit identities;
  security-sensitive kernel APIs consume that context rather than a scalar
  caller ID.
- REQ-002: Process creation derives a child CSpace from concrete parent
  authority, injects it into the new TCB, preserves or attenuates it on exec
  and fork, and closes its handles on exit.
- REQ-003: PID1 alone starts with non-transferable `RootMintAuthority`; once
  PID1 is live, ambient full-authority spawn is sealed and empty CSpaces deny.
- REQ-004: A filesystem-backed ring-3 PID1 service manager verifies a workload
  manifest/image, resolves dependencies, reserves endpoints, starts workloads,
  and stops them in reverse dependency order.
- REQ-005: Service death revokes the old CSpace and delegated grants before a
  fresh policy-derived instance is started; restart is bounded and quarantines
  a restart storm.
- REQ-006: Every workload task belongs to a job, isolation domain, and resource
  domain. Filesystem, process, IPC, network, syscall, and device operations
  fail closed without an explicit handle or domain route.
- REQ-007: Services, agents, and containers specialize one `WorkloadManifest`
  and compile through one policy compiler to a common `SpawnSpec`.
- REQ-008: Agent tool/model/secret/approval operations route through brokers;
  a subagent has a strict subset of its parent authority and approval grants
  are target-bound, expiring, and single-use.
- REQ-009: Native containers are composed from a job, CSpace, isolation domain,
  resource domain, image snapshot, identity, and lifecycle monitor; hostile
  code selects a separately implemented strong-sandbox tier.

## Requirement-to-phase mapping

| Requirement | First delivery phase |
| --- | --- |
| REQ-001 | 0 |
| REQ-002–003 | 1 |
| REQ-004–005 | 2 |
| REQ-006 | 3 |
| REQ-007–009 | 4–6 |
