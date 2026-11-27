# Warm inventory binding retained decoded generation during compiler worker

Status: source repair proposed; runtime and comparable memory verification pending.

The 2026-10-25 Phase3 attempt used producer SHA256
`a2c241a92d96ff76f1b5e5cdc9d337f6528f1b2a1ba5d8cb0aac6803ef352b55`
and selected 1515 sources. Its aggregate guard stopped at 5,870,804 KiB RSS
against 5,859,375 KiB, exit 88, quiescent 1, before publishing objects.
The failure ledger was incomplete. This is not proof of a particular failed
module, nor proof that one allocation owner accounts for the complete peak.

The coordinator authenticates the complete warm inventory only to check its
digest and generation. The old local `current` goes out of scope, but that
does not retire native transient-managed allocations: decoded rows and
canonicalization buffers remained allocated while the coordinator waited for
its compiler worker. Parent parse-closure scratch already had a real owner and
was reclaimed; adding its existing scope again would not repair this gap.

`inventory_binding_scratch.spl` gives only the authentication read a scratch
lifetime. It is intended to retain a text reason and retire decoded inventory
allocations before the next event scan. The caller retains the refresh lock and ordinary
inventory publication logic. Captured pointer bytes, SHA256 validation,
canonical re-encoding, digest/generation checks and existing failure labels
remain required. An active or paused caller scope stays caller-owned.

Do not wrap the complete inventory or source-authority transaction in this
scope: per-file event hashing and snapshot materialization have their own
scratch owners. Broad outer retention would also accumulate source bytes
until the transaction finished. No memory cap, admission check, Any diagnostic
or cache integrity check is disabled by this repair.

Authored regression:
`test/01_unit/compiler/driver/inventory_binding_scratch_spec.spl` has seven
real filesystem/lifetime scenarios: admitted canonical rows, digest and
generation mismatch, tampered immutable bytes, decoder error bytes after later
allocations and another generation read, newly allocated scalar-text promotion
through the actual wrapper ABI, active caller ownership and paused
caller ownership. These scenarios have not yet been executed with a
qualified self-hosted runtime.

Before claiming the memory bug fixed, compare the same source/producer/runtime
and cache state with per-process working set, private commit, elapsed time and
inventory-stage samples. Confirm reduced retained coordinator memory after
authentication and unchanged admission results. Then run the original full
target with normal memory policy. A separately authorized monitor-only
diagnostic can collect logical errors, but does not admit the normal memory
gate or qualify Phase3.
