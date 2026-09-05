# Authenticated positioned-syscall provider v1

> These scenarios exercise the bounded kernel/provider boundary for syscalls 134 and 135. The boundary accepts no raw addresses: it resolves the authenticated caller, file object, registration ID, and buffer slot/generation against the service registries before invoking the canonical positioned-I/O transaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Authenticated positioned-syscall provider v1

These scenarios exercise the bounded kernel/provider boundary for syscalls 134 and 135. The boundary accepts no raw addresses: it resolves the authenticated caller, file object, registration ID, and buffer slot/generation against the service registries before invoking the canonical positioned-I/O transaction.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | `doc/02_requirements/feature/sosix_parallel_qemu_refactor.md` |
| Plan | `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md` |
| Design | `doc/05_design/sosix_parallel_qemu_refactor.md` |
| Research | `doc/01_research/local/sosix_parallel_qemu_refactor.md` |
| Source | `test/01_unit/os/sosix/fs_positioned_syscall_provider_v1_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios exercise the bounded kernel/provider boundary for syscalls 134
and 135. The boundary accepts no raw addresses: it resolves the authenticated
caller, file object, registration ID, and buffer slot/generation against the
service registries before invoking the canonical positioned-I/O transaction.

## Operator contract

- A successful read copies backend bytes into the registered service buffer.
- A successful write sources bytes only from that registered buffer.
- Caller, capability, generation, access, and range mismatches fail before I/O.
- The backend contract is true `read_at`/`write_at`; cursor save/seek/restore is
  outside this interface and is not a valid provider implementation.

**Requirements:** `doc/02_requirements/feature/sosix_parallel_qemu_refactor.md`
**Plan:** `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md`
**Design:** `doc/05_design/sosix_parallel_qemu_refactor.md`
**Research:** `doc/01_research/local/sosix_parallel_qemu_refactor.md`

## Scenarios

### SOSIX authenticated positioned syscall provider v1

#### resolves registered identities and reaches canonical read_at transaction

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = sosix_fs_positioned_syscall_args_v1(
    SOSIX_FS_PREAD_REGISTERED_V1, 41, 73,
    0x0000000900000004, 1, 1, 2)
val result = sosix_fs_dispatch_positioned_registered_v1(
    args, _facts(42), _registry(42), PositionedProviderBackend(bytes: [10, 20, 30, 40]))

expect(result.accepted).to_be(true)
expect(result.syscall_result.value).to_equal(2)
expect(result.registry.buffers[0].bytes).to_equal([0, 20, 30, 0, 0])
```

</details>

#### writes authoritative registered bytes without seek emulation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = _registry(42)
registry.buffers[0].bytes = [0, 7, 8, 0, 0]
val backend = PositionedProviderBackend(bytes: [10, 20, 30, 40])
val args = sosix_fs_positioned_syscall_args_v1(
    SOSIX_FS_PWRITE_REGISTERED_V1, 41, 73,
    0x0000000900000004, 1, 1, 2)
val result = sosix_fs_dispatch_positioned_registered_v1(
    args, _facts(42), registry, backend)

expect(result.accepted).to_be(true)
expect(backend.bytes).to_equal([10, 7, 8, 40])
```

</details>

#### rejects another caller and stale buffer identity before backend dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = sosix_fs_positioned_syscall_args_v1(
    SOSIX_FS_PREAD_REGISTERED_V1, 41, 73,
    0x0000000800000004, 0, 0, 1)
val result = sosix_fs_dispatch_positioned_registered_v1(
    args, _facts(99), _registry(42), PositionedProviderBackend(bytes: [10]))

expect(result.accepted).to_be(false)
expect(result.reason).to_equal("positioned-capability-not-authorized")
expect(result.syscall_result.value).to_equal(-13)
```

</details>

#### rejects authenticated buffer ranges outside the registered bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = sosix_fs_positioned_syscall_args_v1(
    SOSIX_FS_PREAD_REGISTERED_V1, 41, 73,
    0x0000000900000004, 0, 4, 2)
val result = sosix_fs_dispatch_positioned_registered_v1(
    args, _facts(42), _registry(42), PositionedProviderBackend(bytes: [10]))

expect(result.accepted).to_be(false)
expect(result.reason).to_equal("positioned-buffer-range-out-of-bounds")
expect(result.syscall_result.value).to_equal(-22)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** ``doc/02_requirements/feature/sosix_parallel_qemu_refactor.md``
- **Plan:** ``doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md``
- **Design:** ``doc/05_design/sosix_parallel_qemu_refactor.md``
- **Research:** ``doc/01_research/local/sosix_parallel_qemu_refactor.md``


</details>
