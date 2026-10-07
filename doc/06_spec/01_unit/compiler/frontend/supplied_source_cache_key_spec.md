# Supplied source parse-cache identity

Status: six real API criteria authored; not executed. Run against this exact candidate compiler, physical fixture path and a fresh admitted private frontend-cache directory/scope. Cache must be enabled: tests fail rather than silently skip when unavailable. Shared cache must be absent or independently empty for deterministic private-hit counts.

1. Keep the tracked fixture bytes/mtime unchanged. Parse two different supplied source buffers under that path. Assert their distinct function sets and nonempty private entries under each actual supplied digest. The disk fixture deliberately contains neither declaration.
2. Parse the same buffer under original and alias module names. Assert a private-hit counter increment and preserved declaration. This verifies bridge reuse, not independent nominal alias semantics or a shared mutable ParserModule.
3. Parse a missing path; assert normal declarations but no cache-hit/miss counter change. Missing-file admission stays disabled.
4. Supply a stale digest through the public target-receipted entry. Assert rejection before cache hits.
5. Parse equal raw bytes under Windows and Linux target projections; assert target-specific declaration presence/absence.

Additional controlled integration acceptance, unexecuted: change effective compiler/options scope and confirm old entries miss; confirm the release target-receipt and advisory identities remain separated; preserve same-content alias behavior. Use existing M4 parser work and cache hit/miss counters plus OS file-read tracing to distinguish parsing from reconstruction. Excluding fixture setup and cache I/O, the private key computation must no longer open/read/hash the source file; file-existence metadata checking remains. Record cold/warm wall time/RSS and source-read bytes, without asserting an unmeasured speedup.

The driver still validates admitted source membership/content. Passing old buffered source to a low-level frontend intentionally compiles those supplied bytes; this does not authorize publishing them as a current filesystem artifact. Source-newer-than-TLDR policy and full TLDR integration remain separate unfinished requirements.

6. Produce a real flat-pool cache entry through frontend parsing, rewrite its header as v1, require loader rejection, restore current v2 header and require exact pool acceptance. No mock cache response. Migration intentionally misses old private entries; valid shared-CAS hydration remains available and unchanged.
