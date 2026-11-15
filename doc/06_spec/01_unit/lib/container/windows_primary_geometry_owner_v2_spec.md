# Windows primary Geometry owner reducers

Status: **NOT_RUN**. Five authored cases call the actual production
disposition, native-write receipt and endpoint comparison helpers.

Source: `test/01_unit/lib/container/windows_primary_geometry_owner_v2_spec.spl`.

The assertions preserve rejected-before-write, Unknown-after-attempt and
acknowledged-after-HTTP states; reject partial or uncertain completion without
retry; wait for queued completion; require the exact revision/payload tuple;
and reject endpoint server/security drift.

The freshness case takes one actual monotonic sample when executed and models
later completion/cleanup times without sleeping. It checks the original probe
start against the 1000 ms ceiling, a shorter installed timeout and clock
regression. It does not execute a native probe or verify physical elapsed time.

Constructed receipt and endpoint values are test metadata only. They do not
qualify any native connection, adopted session, live issuer, write, size,
acknowledgment or cleanup. In particular, the Boolean acknowledgment state is
not evidence that a native acknowledgment occurred.
