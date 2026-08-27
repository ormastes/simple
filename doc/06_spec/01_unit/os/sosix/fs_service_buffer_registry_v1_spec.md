# SOSIX FS v1 service buffer registration

This manual proves that filesystem services create and retire bounded buffer
registry entries only from authenticated IPC transport facts.

## Register an owned-copy buffer

Given authenticated owner `42` is connected to filesystem endpoint `700`, the
service accepts slot `4`, generation `9`, access flags, and a non-empty byte
payload. It copies those bytes into service-owned storage and returns a receipt
binding owner, endpoint, slot, generation, service registration ID, byte
length, access, and owned-copy memory mode. No address is carried on the wire,
and the receipt does not claim shared memory.

## Refresh service storage

An owned-copy refresh carries the complete replacement byte payload through
the same authenticated IPC channel. The service accepts it only when transport
owner/endpoint and every receipt field match the live entry and the length is
unchanged. A forged registration ID or foreign owner leaves storage unchanged.

## Retire and reuse

Retirement requires the same authenticated binding, erases the service-owned
bytes, marks the entry inactive, and advances its generation. The old
generation is stale. Reuse requires the advanced generation and receives a new
monotonic service registration ID.

## Authoritative dispatch and commit

The validated dispatch plan carries the service registration ID plus buffer
slot and generation. Before backend dispatch, the service looks up and copies
the authoritative registry bytes using an exact active owner/ref/registration
match; callers cannot inject an alternate array. A READ result is committed
only when that same identity is still active and the full storage length still
matches. Retirement or reuse makes an in-flight old-generation commit stale.
