# Streaming source-owner reclamation evidence — 2026-08-22

The streaming compiler retains two independently allocated copies of every
physical source through HIR: `SourceFile.content` and
`CompileContext.source_contents_owner`. Logical module aliases share the
second copy and therefore do not multiply payload bytes.

The new release boundary is after successful HIR lowering and post-HIR layout
validation. It is not reached on parse/HIR/validation errors. HIR cache hits
still pass through it; HIR shard workers exit before it; VHDL is excluded from
the streaming-surface lane and retains its source closure for artifact output.

Complexity remains O(number of logical sources), matching the adjacent source
reclamation loop. The loop performs no payload copy and no heap allocation;
it makes one registry-checked `rt_string_free` dispatch per logical row, then
clears the owner array so no freed alias remains observable.

Host ownership model command:

```sh
sh scripts/check/check-streaming-source-owner-reclaim-model.shs
```

The model uses 128 physical 256-KiB sources and 384 logical aliases. Before
release, modeled live source payload is 64 MiB. Releasing only the duplicate
owner removes exactly 32 MiB and leaves the original 32 MiB live until the
adjacent source-owner release. The generated `build/.../model.env` and
`time.env` retain exact modeled bytes, elapsed time, and host peak RSS.

Measured on this host: 0.16 seconds elapsed, 67,584 KiB peak RSS, exactly
33,554,432 modeled owner bytes reclaimed, and zero owner allocations live
after release. This is a lifecycle model rather than a compiler throughput
claim; source-matched compiler measurement remains gated on an admitted
self-hosted binary.

The Simple optimizer was intentionally not run: the current source-matched
self-hosted compiler is not admitted, and using the Rust seed would not be
valid optimization evidence.
