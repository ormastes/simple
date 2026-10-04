# SHA stream owner dependency

Date: 2026-10-04. Release research base: `f5fec9ccf8cb`.
This repairs the existing item4 retained-file/SCV dependency; no requirement is
removed and no new cryptographic format is introduced.

`Sha256StreamV1` is a value owner. Its scalar counters, block, schedule and
digest words must advance together. The constructor stays a free function;
reset, update, update_byte, finish_hex and zeroize are mutable methods. Internal
compression and padding/push are mutable methods too. The old by-value mutating
functions are removed so unmigrated callers fail visibly at compilation.

Update validates finished state and the SHA bit-length bound before touching
buffers. Finalization is one-shot, preserves the message-byte count, and uses
the same mutable owner while inserting padding. Zeroization disables the owner
even if a native wipe report fails; reset explicitly restores the initial state.
One-shot SHA APIs and digest wire formats remain unchanged.

Local callers retain `var` streams. AST and module-surface helpers return their
updated enclosing value; terminal digest helpers consume a local copy. Their
callers must not reuse the consumed value. The schema generator and checked-in
AST projection receive matching edits. Mount snapshot rows copy the stream to a
mutable local, then explicitly write it into the updated row. DBD stores a
mutable nested stream inside its mutable credential owner.

SCV start returns the updated domain-prefixed owner, hydration retains it across
chunks, and finish consumes a local owner to append dependency frames. SCV
tests inspect the caller's counters and a fixed external envelope digest.

The separate compiler canonical-stream wrapper still mutates an enclosing
value through void free functions. Migrating its SHA calls does not repair its
outer counters, errors or frames. Track that separately in
`doc/08_tracking/bug/semantic_canonical_stream_owner_writeback_2026-10-04.md`.

## Acceptance and evidence

| Criterion | Executable evidence | Current state |
|---|---|---|
| Original counters persist through chunks and block compression | sha256_stream_owner_spec, seven 55/56/63/64/65/119/120-byte vectors through whole, irregular and byte updates | Authored; UNRUN |
| Finalization once, padding, reset | owner spec fixed abc/empty vectors and state assertions | Authored; UNRUN |
| Overflow and post-finish rejection leave owner unchanged | owner spec counters and buffers | Authored; UNRUN |
| Wipe disables original owner; explicit reset restores it | owner spec zero buffers and known digest | Authored; UNRUN |
| SCV domain and chunks survive API boundaries | db_evidence_stream_spec independent envelope vector and counters | Authored; UNRUN |
| All production callers compile and preserve behavior | core/lib/MCP checks, native core smoke, SCV hydration, mount/DBD and compiler suites | UNRUN |

The seven SHA vectors and SCV digest were independently calculated with .NET
SHA256. That validates expected constants, not Simple execution. Source review
was performed independently by linker_acceptance; no runtime PASS is claimed.
