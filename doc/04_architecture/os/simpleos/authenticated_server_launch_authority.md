# Authenticated server launch authority

`os.kernel.loader.server_launch_grants` is the single policy owner for the
filesystem-launched `/SERVERS.ELF` process on x86_64, AArch64, and RV64.  All
three authenticated-media adapters select
`SPAWN_RECIPE_AUTHENTICATED_SERVER`; they do not reuse the generic
`APP_LAUNCHER` recipe.

The pouch contains seven non-delegable grants: execute `/SERVERS.ELF`, read the
complete leaf paths `/SYS/SERVER.HTM`, `/SYS/SRVDB.KEY`, `/SYS/SRVDB.CRT`, and
`/SYS/SRVDB.PK8`, and listen on TCP ports 8080 and 5433.  It contains no file
write/create, network-connect, process-spawn, filesystem-root, DBFS, FAT32, or
mount authority.  `future_server_data_authority` is an empty descriptive field,
not a capability; adding persistence requires a separately reviewed storage
owner and cannot silently authorize `/SERVER.SDN`.

The generic C-space mint preserves parent-token provenance and assigns bounded
generations.  Immediately before authenticated scheduler publication,
`capability_set_bind_owner` reconstructs the small pouch with the scheduler's
new task id while preserving kind, generation, token id, parent id, and depth.
The TCB therefore never publishes tokens still owned by the spawning task.

Construction and rebinding are each O(g) time and O(g) storage for `g = 7`.
They run once per authenticated process publication; no request-path lookup,
dispatch, allocation, or per-connection copy is introduced.

The former ARM compatibility policy built 24 tokens for this image (four broad
launch tokens, two reads, and eighteen `/SERVER.SDN*` read/write/create tokens).
The shared policy builds seven exact tokens, a 17-token / 70.8% reduction in
launch-time pouch storage and construction.  Runtime timing/RSS and optimizer
output require the admitted self-hosted binary; no seed substitution is valid.

## Dedicated DBD migration boundary

`os.kernel.loader.dbd_launch_grants_v1` owns a separate ten-grant pouch for
the canonical `/sys/services/dbd` image: execute that image, read only the
database credential/certificate/private-key leaves, read, write, and create only in the
canonical `/srv/data/db` subtree, and listen only on 5433. It has no ambient
filesystem authority, `/SYS/SERVER.HTM` read, or 8080 listener. The protected DBFS startup
receipt registry accepts a closed role set of legacy `/SERVERS.ELF` and this
DBD image; `/WEB.ELF` is outside that set and cannot redeem a server-data
receipt.

Direct open/create and rename dispatch copy each userspace pathname once,
canonicalize that kernel-owned value, and check authenticated managed-server
paths against the authoritative current scheduler TCB pouch. An unavailable,
unowned, stale, or non-pledged TCB is a terminal denial with no IPC-capability
fallback; unmanaged paths retain the existing IPC manager check. The same
canonical value is later used for namespace/backend selection. The generic
empty-path precheck is intentionally absent for those calls because it cannot
consume an attenuated subtree grant. Managed DBFS descriptor binding remains
fail-closed with `ENOSYS`; until that owner is wired, DBD cannot advertise live
filesystem durability. Its bounded journal also still uses whole-journal
transactional replacement per mutation, an explicit O(total journal bytes)
performance blocker for the future append/checkpoint owner.

The task-capability adoption wiring for the new DBD recipe uses one shared
filesystem-exec pouch owner on ARM64 and RV64. This is deliberately not a
claim of x86 runtime launch parity: x86 authenticated adoption receives
caller-owned capabilities and has no local minting seam to replace safely.
