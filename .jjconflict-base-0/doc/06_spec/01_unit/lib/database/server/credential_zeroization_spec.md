# Database Server Credential Zeroization

Source: `test/01_unit/lib/database/server/credential_zeroization_spec.spl`

Evidence class: `host-fixture`. The scenarios exercise the production
credential registration, authentication, and bounded wipe owners in memory;
they do not prove guest RAM erasure after shutdown.

## Scenarios

- Byte registration authenticates identically to the legacy text path while
  wrong, empty, and unregistered credentials fail closed.
- A caller can wipe its input buffer after registration without invalidating
  the retained digest used for later authentication.
- Exact-range zeroization clears every requested byte while preserving adjacent
  canaries; out-of-bounds ranges fail without modifying the allocation.

