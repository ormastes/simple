<!-- codex-design -->
# Design - Web DB Primitive Hardening

## Web
Add `closed: bool` to `BoundedChannel<T>`. `close()` sets it, `is_closed()` exposes it for tests, and `try_send()` returns `Err(OverflowError)` without enqueueing after close.

## HTTP/Web Framework
Replace placeholder branch bodies with `continue`, `return`, response sending, or bounded sleep. Handle `ConnectionAction.WriteResponse` and `ConnectionAction.SendFile` explicitly in worker completion paths.

## Database
Use a production system spec with temporary SDN files. Cover save/load, table mutation, soft delete, valid row filtering, malformed import rejection, and query filtering/order.

## Primitive
Keep primitive usage and API lint specs in the verification set. Do not change compiler behavior unless those specs fail.
