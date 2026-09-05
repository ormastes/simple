# Architecture: SimpleOS server execution matrix

## Decision

Use one receipt contract across three target modes:

```text
host controller -> target launcher -> filesystem executable -> HTTP/DB owner
       ^                                                        |
       +--- bounded SimpleOsServerExecutionReceiptV1 -----------+

parent server/DB/filesystem owner -> copied/frozen compute input
                                 -> CPU or optional device worker
                                 -> bounded result -> validate -> owner commit
```

ARM64 QEMU and UNO Q are distinct transports and may not substitute for one
another. A launcher resolves executable bytes from the target filesystem; a
marker or host process cannot satisfy that boundary. Persistence credit
requires termination/reboot followed by a new read through the same public
protocol.

The Linux comparison uses adapters around public protocols. It does not embed
nginx, PostgreSQL or SQLite into Simple. CUDA is loaded only by an optional
compute adapter through the established dynload owner. Network framing,
authentication, transaction validation, durability and filesystem mutation
remain CPU parent responsibilities. The device returns data plus length,
backend identity and checksum; the parent validates all fields before use.

## Failure policy

Missing target drivers, syscalls, hardware backends or receipt fields fail the
cell closed. Unsupported hardware is a blocker, not a successful fallback.
