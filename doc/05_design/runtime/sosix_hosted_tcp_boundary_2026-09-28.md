# Hosted TCP compatibility boundary

Status: source candidate against `267b99c8c17`; runtime acceptance pending.

This slice follows the portable host boundary direction proposed in the
[unification plan](../../01_research/runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md).
It does not select the pending F1 integration order or F2 positioned-write
contract. It preserves the current hosted synchronous API.

## Ownership

`nogc_sync_mut.io.tcp` retains TcpListener, TcpStream and TcpSocket lifetime,
validation, errors and partial-I/O loops. Its twenty-three TCP runtime
operations now import `nogc_sync_mut.sosix.network`. That facade uses braced
aliases of `nogc_sync_mut.sffi.net` functions. The SFFI owner declares each
raw TCP ABI once and explicitly publishes those wrappers for the SOSIX facade.
The sync layer never imports the async layer, and there is no new scheduler or
descriptor table.

All parameters, return types and existing unsafe call blocks are preserved.
The SFFI byte-read return now matches the consumer's `[u8]?` and the native
provider's nil-on-failure behavior. The previously absent peer-address and
shutdown SFFI wrappers have their existing signatures. Redis, UDP, DNS and
other network consumers remain outside this slice. Native compilation must
still confirm that the alias route and the nullable result lower correctly.

## Verification

The integration spec at
`test/02_integration/lib/sosix/hosted_tcp_boundary_spec.spl` uses an ephemeral
loopback port, connects through TcpStream, accepts through SOSIX, exchanges two
newline-terminated messages, checks a successful nullable byte read, exact
remaining text/counts, EOF as an empty array, and closes real handles.
Connect, accept and reads have one-second limits. It also checks existing public
negative-descriptor guards. Provider unavailability is a failure, never a skip.

Source checks compare all twenty-three declarations with the provider, require that
no migrated raw declaration remains, resolve every alias, and compare normalized
production code with the baseline after reversing the route rename. Runtime
testing remains blocked: the available release binary reports rc.1, but no
receipt establishes that it matches this source. No runtime PASS, native alias
cost, cross-platform support or RU-040 closure is claimed. Whole-tree gates
must run from a complete checkout with a source-qualified runner.

## Handoff

Sidecar lanes: N/A. Implementation owner: SOSIX hosted TCP seam lane. Merge
owner and final reviewer: parent session. No commit or push is authorized in
this lane before parent review.
