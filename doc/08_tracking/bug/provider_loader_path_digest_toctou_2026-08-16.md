# Provider path digest check is not bound to the mapped file handle

Date: 2026-08-16
Status: Open

## Impact

`provider_admit_dynamic_v1` reads and hashes the declared provider path before
calling `dynlib_open(path, ...)`. This correctly rejects a wrong byte identity
before mapping in the ordinary case, but the file can be replaced between the
read and the path-based open. Native library initializers may execute during
open, so hashing the path again afterward would detect the race too late.

The current source must therefore not be described as cryptographically
binding the locked artifact digest to the mapped image under a hostile writer.
Path, digest shape/value, capability, host/interface version, symbol
callability, and query stability checks remain useful fail-closed checks.

## Unblock condition

1. Add an owner API that opens the provider without following a mutable path,
   returning an immutable file/descriptor handle plus identity metadata.
2. Hash the bytes from that handle, then map/load from the same handle (or from
   an atomically published content-addressed immutable snapshot).
3. Bind target/signature evidence to the same admitted handle before any
   initializer or provider code can run.
4. Add a controlled replacement-race fixture and one admitted native run.

Do not paper over this with a second path hash after `dynlib_open`; that is
diagnostic only and cannot undo already executed load-time code.
