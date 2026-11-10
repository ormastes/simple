# Catalogue service capabilities do not match live syscall requirements
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** Partially resolved 2026-09-16 — named IPC live; endpoint generations and
exact-endpoint shims landed and statically verified 2026-11-11 (lane ne4);
confinement-spec execution BLOCKED on VirtMemManager tri-def (see addendum)

## Evidence

`src/os/kernel/loader/root_service_catalog.spl` correctly mints exact named
authority for its service children, for example `IpcListen("vfs")`,
`IpcConnect("net")`, and `NetListen(80)`.

The original generic syscall dispatcher checked IPC operations with
`IpcListen("")` / `IpcConnect("")`; a child holding `IpcListen("vfs")` could
not pass, and an implementation that loosened the check would have created a
wildcard endpoint bypass.

As of the 2026-08-11 critical-path implementation, syscall IDs 20–23 and
132–133 resolve the actual endpoint name from the live port table and check
that exact typed capability. Creation/connect copy and validate a user name
once, so the authorization and operation use the same bytes. Receive also
requires live ownership. The bound copied-payload path mints a bounded,
one-shot reply permit only after a request has been copied successfully; it is
consumed after the matching reply and removed on task exit. This makes replies
possible without granting a service wildcard access to all client endpoints.

Do **not** solve this by adding wildcard IPC or port-zero capabilities to the
catalogue. That would erase the named least-authority policy and create an
ambient endpoint-access bypass.

## Required resolution

1. Replace numeric endpoint IDs with typed endpoint handles carrying a
   generation and connect/listen rights; the current monotonic IDs avoid reuse
   but are not yet first-class CSpace handles.
2. Make bind/connect authorize their actual port/route; `listen` and `accept`
   must operate only on a socket previously bound under that authority.
3. Add live scheduler tests proving `vfs` cannot connect to `net`, HTTP cannot
   bind another port, and no named capability authorizes an unrelated endpoint.

This is independent of the missing service payload/driver broker work. It must
be resolved before any catalogue service can be accepted as capability-confined.


## 2026-11-11 addendum (lane ne4, batch p3-ne4-20261111)

Re-verified against release/1.0.0 tip (fa6366ca8bf5) on this worktree.

Required resolution #1 (generation-carrying handles): LANDED.
`src/os/kernel/loader/root_service_catalog.spl:173` mints capability
tokens with `generation: 1u64`; `test/01_unit/os/kernel/ipc/capability_mint_spec.spl`
pins monotonic generation increments on re-mint
(`expect(caps.caps[0].generation).to_be_greater_than(200u64)` etc.).
First-class CSpace handles remain a design aspiration, but the
no-silent-reuse property the generation was asked for is implemented and
pinned.

Required resolution #2 (bind/connect authorize actual port/route):
LANDED in the live ring-3 shim path. `src/os/kernel/abi/syscall_shim_net.spl`:
- `spl_shim_net_direct_bind_check(address, port)` (line 50) requires
  BOTH `CapabilityKind.NetBindIpv4(address: address, port: port)` AND
  `CapabilityKind.NetListen(port: port)` for the exact copied endpoint.
- `spl_shim_net_direct_listener_check(port)` (line 61) requires the exact
  `NetListen(port: port)`.
- `spl_shim_net_capability_check` (line 21) docstring explicitly forbids
  substituting a port-zero grant for the exact check.
Note the generic `src/os/kernel/ipc/syscall.spl:_cap_check` is documented
NOT-YET-WIRED in production (module comment lines 170-173 and the
function docstring at 175-181); production enforcement lives in the
direct shims enumerated above. Spec-path `_cap_check(IpcConnect(""))`
calls are spec-only and marked as such.

Required resolution #3 (live scheduler confinement tests): SPECS EXIST
but are currently not executable. The exact properties are pinned in
`test/01_unit/os/kernel/ipc/portable_net_shim_capability_spec.spl`
("does not borrow socket creation from outbound connect authority",
"admits a separately granted socket creation right", "denies a bind when
the IPv4 address differs from the pledged grant") and
`net_listen_broker_spec.spl`. However every spec importing
`os.kernel.scheduler.scheduler` now fails at load under the current tree
with `error: semantic: ambiguous type VirtMemManager: defined in
src/os/kernel/arch/x86_64/paging.spl, src/os/kernel/memory/vmm.spl,
src/os/kernel/memory/vmm_core.spl and none of them is imported by
<entry>` — three genuine struct definitions surfaced by the fail-closed
co-compiled duplicate resolution (owner decision 2026-11-09,
10e216d19f8c). This is unrelated OS-arch debt, not a regression of this
bug's mechanism; a minimal probe importing only the net-shim authority
fails identically, so it is not spec-specific.

Verdict: mechanism FIXED and statically verified; #3 execution
BLOCKED on the VirtMemManager tri-def. Grant command for the unblocking
lane: an OS-owner decision renaming/merging two of the three
`VirtMemManager` definitions (or an explicit entry import), then re-run:
  SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test \
    test/01_unit/os/kernel/ipc/portable_net_shim_capability_spec.spl \
    test/01_unit/os/kernel/ipc/capability_mint_spec.spl \
    test/01_unit/os/kernel/ipc/net_listen_broker_spec.spl \
    --mode=interpreter --no-cache
