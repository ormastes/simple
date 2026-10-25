# Scoped allocation claim repair

Candidate scope: Rust runtime portion of P0–P3, based on `61b53c38b7a`.
P4 rc-root APIs and their incidental donor interaction test are excluded by the
integrator. This does not qualify Phase 3, bootstrap, or full CLI execution.

A module/session ledger stores `{ptr, birth, owner}`. Canonical scoped metadata
shares the allocation membership mutex. Birth and owner counters never reset or
wrap. A scoped claim compares live membership and all key fields before reading
any header. The successful claim retires membership and scoped metadata, captures
type/size, and authorizes shared disposal exactly once. Ordinary typed free paths
also claim before disposing array/dict auxiliary storage or reading layout data.
Deep-free keeps its existing exclusive-subtree precondition and uses the same
claim/dispose path in its commit phase.

Persistent allocation registration retains the existing membership-only set.
Only module/session tracking creates scoped metadata. Module transfer records the
destination under canonical source authority before changing owner and withdrawing
the source ledger. Foreign-thread free retires canonical metadata and never
mutates another thread's ledger. Old entries are safe tombstones by identity.

Closure retain publishes pins while holding pin -> registry order. Typed
non-closure frees use one registry lock. Untyped frees take pin -> registry from
the first observation; scoped closure claims may inspect the registered type and
then reacquire pin -> registry, rechecking the exact birth/owner. Pinned claims
remove scoped authority and leave final disposal to the orphan's last release.
No user cleanup runs under either lock.

On a 64-bit host, ledger payload grows from 8 to 24 bytes per entry. Canonical
scoped-map payload is 32 bytes per entry (address plus key), session owned-map
payload grows from an 8-byte set key to a 32-byte map entry; module index remains
16 bytes and ambiguous promotion keys grow from 8 to 24 bytes. Hash-table load
factor/control bytes, allocator overhead, and spare Vec capacity are additional.
Scoped allocation adds a registry lock/map insert; ownership probes and transfer
add canonical checks. Untyped legacy unregister adds a pin lock. There is no
zero-overhead or no-regression claim: representative timing/RSS comparison is a
separate required qualification gate.

Deterministic tests retain real allocated storage while retiring its canonical
lifetime and registering the same address with a new birth. They do not depend
on malloc returning a recycled address. They cover same/foreign-thread ownership,
module transfer/end, typed frees, exactly-once disposal, pinned closures, stale
unmapped keys, nonwrapping counters, and measured payload sizes. The old backing
storage is physically disposed only after the final successful claim.
