# Private admission fixture (authored, unrun)

Build `provider.spl` as a Linux dependency-free shared object exporting only the
fixed four-i64 entry. The production ELF gate must accept the resulting artifact;
any inability to build that profile is a blocker, not a passing skipped test.
Launch `main.spl`'s compiled executable in a fresh process with isolated user
configuration and scratch paths. Its host trust root must be the Ed25519 public
key for seed bytes 0..31, provisioned by the test launcher, never through a loader
argument. Arguments are the absolute artifact path and fresh scratch directory.

The harness uses real signed bytes, exact library mapping and the public generic
lease owner. That generic lease must not create a private approval row. Only the
normal host-policy loader may create the positive selection. It also checks
changed-request, identity corruption and unissued-token refusal. It does not
claim successful provider dispatch: the fixture entry deliberately returns -17.
No build or execution has been performed for this fixture.

Run fresh processes with optional fourth argument `capacity` and `concurrent`.
The first proves exactly 127 further successful mappings after the initial
admission and then an explicit capacity refusal. The second runs four joined
workers with 40 requests each and asserts the same total; no mutex is held over
mapping or signature work. Requests are immutable parent loans retained through
join, workers own local results, and only scalar counts cross back. Existing
approved tokens remain usable after capacity exhaustion. These scenarios are
authored/unrun, not a thread-safety or physical-memory qualification.

The production quota is 128 **mapping attempts per process**, including in-flight
and failed attempts. Attempts are reserved only after policy/artifact checks,
but before the exact-map effect, and never refunded because a failed load can
retain a sealed snapshot descriptor. This staging limit bounds that retained
resource; it does not prove a global RSS ceiling or permit hot unload.


Transport prerequisite mode (authored/unrun): run the parent fixture with fourth
argument `transport`; it writes canonical `transport.sdn` and the expected scope
SHA to the scratch directory. Build `transport_child.spl` separately and launch
it in another process with that SDN path, the scope SHA, and `accept`. It receives
no signing seed/token and must independently read host trust and map the pinned
provider before creating its actual driver. For negative runs in fresh processes,
replace the policy, signature or artifact after parent publication and use
`reject`; restore the original files between independent cases. Missing transport
and wrong scope have direct assertions. The parent test key remains confined to
the isolated fixture; production transport cannot choose a trust key.

This is an application-boundary prerequisite, not a completed managed-worker
route. Group/index manifest, provider-bound index variant, receipt/cache transport
remain unwired; native-build continues to reject selected managed/shard requests.
