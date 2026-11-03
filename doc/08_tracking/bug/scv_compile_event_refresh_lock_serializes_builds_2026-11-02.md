# SCV compile-event refresh serializes concurrent builds

Status: open; repair candidate awaiting qualified runtime verification.

The canonical BugDB report identifies a repo-wide
`build/scv/compile-events/refresh.lock` held across source discovery, Git
queries, hashing, cursor reads and publication. PR #5932 only changed the
separate workaround-index lock and explicitly deferred this defect.

## Candidate 2026-11-03

The refresh owner captures CURRENT, its decoded cursor and authenticated
membership paths under a descriptor lease. It releases that descriptor before
inventory-generation authentication, Git queries, aliases, source hashing and
journal discovery. The membership array is a snapshot copy: the on-disk old
record may be retired by a concurrent successful publisher without invalidating
an in-flight observer. Ordinary publication retains immutable generation blobs.

Before no-event admission, membership publication, inventory publication or
record cleanup, the observer reacquires the same refresh lock and compares the
complete CURRENT byte digest to its captured snapshot. A superseded snapshot
cannot publish or reclaim records. It releases its current descriptor and may
observe again once; all other failures return immediately. Two superseded
attempts return a named contention error. Publication's existing independent
CAS and atomic CURRENT rename remain unchanged. Descriptor ownership is
explicit, and unlock failures are never reported as successful releases.

The publication phase still serializes inventory application and atomic
readback; this repair removes source discovery and authentication from the
long critical section. It does not promise zero contention or a measured
speedup without runtime evidence.

## Required evidence

`test/02_integration/app/compiler_inventory_refresh_interleaving_spec.spl`
contains three real-behavior examples:

- A paused observer releases its actual OS lease while another real refresh
  publishes changed membership and retires the old blob. Stale resumption is
  refused, the newer record survives, and double release cannot unlock the
  next owner's descriptor.
- Two OS-thread owners call the ordinary public refresh API against the same
  dirty source; both must finish successfully and preserve its exact digest.
- A pointer suffix mutation after NUL is refused using complete-byte binding;
  restoring authority permits a no-event refresh with unchanged CURRENT.

The deterministic schedule proves ownership interleaving independently of
scheduler timing. Run it alongside existing no-event refresh, corrupt
membership, failed publication and membership-GC regressions. Compiler/core/lib
and MCP/LSP checks and runtime smoke gates also remain required.

Runtime verification: **TEST_BLOCKED** on this Windows host, which has no
qualified self-hosted CLI. Zero behavioral examples executed. The tracked Rust
seed was not used. This is a draft candidate, not a verified fix or closure.

Static validation passed: scoped snapshot/discovery/publication/reclamation
source ordering and the two-attempt retry bound; working and staged direct
env/runtime guards; whitespace check; tracked `doc/06_spec` executable spec
count zero. These checks do not establish runtime or performance correctness.
