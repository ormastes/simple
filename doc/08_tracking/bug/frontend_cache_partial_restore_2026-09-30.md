# Frontend cache accepted malformed pool frames

## Evidence

Linux producer `203e210012adcfb21d29571506bfa9e39cb56eb1aabbd89a68c8efd20212533b`
completed streaming surface parsing and wrote 1060 frontend cache entries.
Its subsequent HIR restore emitted unhandled declaration kinds with empty tags.
The run then aborted at a separate ordinary frontend call inside a HIR-owned
transient scope. Neither a successful warm build nor compiler admission occurred.

A source-format audit of retained cache
`e032719bd5897969f57831432e8d9bc3d2c6eaff4ab8f1aebc62c472e613dd00.fpc`
found declaration count 14 but 27411 entries in both the memory-bank and
parameter-default pools. Framing later encountered `0,0` where a pool length
was expected. The metadata owner separately identified omitted pool resets.
This does not establish that every blank-tag diagnostic has the same cause.

The cache reader used the general legacy cursor. Its integer conversion did
not reject noncanonical numeric fields; the aggregate restore did not require
complete frame consumption or declaration-pool cardinality consistency. Such
partial restores must be cache misses and must never count as successful hits.

## Fix contract

- Frontend cache uses an additive canonical cursor, preserving general legacy
  codec behavior. Invalid integer fields and extra frame data reject the entry.
- Canonical frames require the serializer's final newline. The split cursor
  may retain that single terminal empty field, but no additional empty frame.
- Aggregate restore requires consistent declaration metadata arrays. All
  restore units run before the aggregate verdict; on rejection, the existing
  parser initialization resets pools before a real parse.
- Metadata reset and in-place restoration preserve owner lifetime. Assembly
  placement is now serialized. Codec v2 invalidates previous FPC headers using
  the normal version contract; old cache files and native objects are retained.

## Regression evidence

`flat_pool_cache_canonical_frame_spec.spl` and its native fixture cover valid
integers, malformed lengths/scalars, truncation, trailing bytes, terminators,
fresh independent frames, and unchanged legacy behavior. The borrowed-scope
integration fixture injects persisted corrupt frames and requires a fresh parse
in the same process with correct counters and caller-owned cleanup. Metadata
regressions separately cover reset and restored values.

The first native codec fixture build with producer 203 failed during MIR
lowering, including unresolved reader methods and UTF-8/SIMD dependencies.
No executable was produced and no runtime PASS is claimed. Retest with the
corrected producer is required. Canonical BugDatabase registration remains
pending a working supported registration executable; no ID is fabricated.
