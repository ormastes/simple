<!-- codex-design -->
# DomainArena V2 detail design

The implementation is in
`src/lib/nogc_sync_mut/mission_critical/domain_arena_v2.spl`.

The factory returns `DomainArenaV2Creation.Created` or
`DomainArenaV2Creation.Rejected`. It performs all scalar validation before
calling the fixed bank constructors. Two private `DomainArenaStorageBankV2`
values each contain one byte bank and three parallel reference banks
(offset/size/mint). The inactive bank is cleared at checkpoint and rollback;
the active bank is never touched by staging writes.

`DomainArenaV2.try_allocate` mints an exact span and records it in the staging
reference bank. `write_byte` accepts only a minted staging span. `read_byte`
accepts only a minted span found in the committed bank, enforcing staging-only
writes and committed-only reads. `commit` requires the opaque owner capability
and a matching checkpoint, then publishes via the private authority state.

The V2 state hash is intentionally cold-path: it frames schema 2, profile and
committed metadata, and every committed byte. The V1 hash and the existing
allocation producer are not modified. Focused unit coverage exercises rejection
before allocation, isolation, exact spans, rollback, and V2 byte evidence.
