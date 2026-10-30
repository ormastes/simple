# Semantic library mode native fixture

Status: NOT_RUN. Native argv, admission/resource gates, exact stdout, negative diagnostics and fresh/warm/interleaved cache matrix: `doc/03_plan/sys_test/configured_library_mode_native.md`.

The common `src/lib` root intentionally contains competing implementations. The command supplies that root, never a physical family directory. Ordinary entries live under `src/app`, preserving the production logical namespace rules. `mixed_entry.spl` combines configured app NoGC with an explicit GC owner and a common named/wildcard re-export chain. Negative entries must not obtain an absent owner or symbol from another family.

The separate `lib/gc_sync_mut/project/src/app/ancestor_entry.spl` path deliberately places an application beneath an unrelated family-looking ancestor. Its actual canonical owner is `app.ancestor_entry`; NoGC configuration must still choose the NoGC provider under the admitted `src/lib` root. `src/app/no_imports.spl` supports the retained-registry replay-mode refusal independently of import resolution.
