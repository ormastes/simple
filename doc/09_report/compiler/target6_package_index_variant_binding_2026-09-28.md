# Target 6 graph variant binding (2026-09-28)

The earlier graph record had no explicit configuration-variant digest. Its
root identity included the variant, but a warm reader accepted a separately
supplied expected variant without comparing it to a stored variant field.
That made the route's variant check indirect and hard to audit.

Graph generations now use schema V2 and store the canonical variant digest.
The builder writes it, the record validator requires a 64-character digest,
and V2 action digests include it. The warm route rejects V1 records,
cross-variant records, and empty graphs. Schema V1 remains readable for the
snapshot-only admission binding, whose variant field must be empty. This is
a schema migration, not a production graph cutover: admission still publishes
only the V1 binding until typed graph facts and a graph publisher are wired.

Focused evidence before the final action-digest and empty-graph edits:

- Bootstrap-interpreter package-index, route, and cold-draft specs passed
  (3/3, 5/5, and 6/6 respectively).
- A 28-unit Stage2 native compare-and-publish probe built and passed with a
  V2 graph record. Its log and binary are under `build/mini_builds/target56_index_v2_*`.

Final qualification is **not passed**. After the action-digest and route edits,
the focused interpreter spec timed out at 180 seconds. Two no-stub native
builds also timed out at 180 and 120 seconds; the latter used the simplified
action-digest expression. The native compiler reached about 40 GiB RSS in
these attempts. These were timeouts, not assertion failures. The required
full CLI, SPipe, startup, and performance gates remain open. Do not use this
partial evidence as a Target 6 completion claim.

The bounded native-build memory issue is tracked in
`doc/08_tracking/bug/target6_focused_stage2_native_build_memory_2026-09-28.md`.

Next, diagnose the large native compile from the retained command/logs with
an isolated source closure, then qualify V2 action digest, round-trip, warm
route, and concurrent graph publication. Production still needs typed
TLDR/SMF/archive fact generation, a graph publisher, Git/SCV event admission,
and the full native performance cohort.
