<!-- codex-system-test -->
# System Test Plan: SOSIX Process Sharing

## Scope

This plan covers the SOSIX user-facing process-sharing contract:

- immutable dataset creation, mutation-before-seal, seal, and read-after-seal behavior
- bounded queue payload transfer and readiness bits
- sealed dataset attachment to queue messages
- rejection of unsealed dataset attachments

Kernel capability, address-space mapping, and POSIX wrapper behavior are excluded from this test slice.

## Requirements

| Requirement | Description |
|-------------|-------------|
| REQ-SOSIX-SHARE-001 | SOSIX datasets must be mutable only before seal and readable as immutable shared data after seal. |
| REQ-SOSIX-SHARE-002 | SOSIX queues must deliver bounded message payloads and expose read/write readiness. |
| REQ-SOSIX-SHARE-003 | SOSIX queues must transfer sealed dataset handles and reject unsealed dataset attachments. |

## Execution

Run the focused executable unit API spec:

```bash
bin/simple test test/unit/os/sosix/share_api_spec.spl
```

Run the system feature spec:

```bash
bin/simple test doc/06_spec/app/os/feature/sosix_process_sharing_spec.spl
```

Run the full SOSIX unit suite before merging with adjacent SOSIX changes:

```bash
bin/simple test test/unit/os/sosix
```

## Traceability

| Requirement | Test File | Test Cases | Coverage |
|-------------|-----------|------------|----------|
| REQ-SOSIX-SHARE-001 | `test/unit/os/sosix/share_api_spec.spl`, `doc/06_spec/app/os/feature/sosix_process_sharing_spec.spl` | create, seal, read, reject post-seal write | Full |
| REQ-SOSIX-SHARE-002 | `test/unit/os/sosix/share_api_spec.spl`, `doc/06_spec/app/os/feature/sosix_process_sharing_spec.spl` | send, receive, payload bytes, readiness restoration | Full |
| REQ-SOSIX-SHARE-003 | `test/unit/os/sosix/share_api_spec.spl`, `doc/06_spec/app/os/feature/sosix_process_sharing_spec.spl` | sealed attachment transfer, attached dataset read, unsealed rejection | Full |

## Pass Criteria

- All SPipe files load and execute without failures.
- Tests use only built-in matchers.
- No test relies on external process state; every case calls `sosix_share_init()`.
- Unsealed dataset attachment attempts leave the queue unreadable.
