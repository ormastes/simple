# `driver_native_module_source_identity` is defined TWICE in one file

- **Status:** OPEN (2026-09-13)
- **Found by:** BOOT-12 while fixing site 12
  (`stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13.md`).

`src/compiler/80.driver/driver_aot_native_output.spl` defines the same free
function at **:844** and again at **:895**:

```
fn driver_native_module_source_identity(ctx: CompileContext, module_name: text) -> text:
    val (_, identity) = driver_native_frozen_source_lookup(
        ctx.source_paths_owner, ctx.source_contents_owner,
        ctx.source_module_names_owner, module_name)          # :844
...
fn driver_native_module_source_identity(ctx: CompileContext, module_name: text) -> text:
    var identity = ""
    for source in ctx.sources:
        if source.module_name == module_name:
            identity = sha256_text(source.content)           # :895
```

The two read DIFFERENT carriers (the owner projection vs `ctx.sources`), so
which one the single call site at **:1761** binds is not obvious from the
source, and the build's own
`compiler_cross_module_private_symbol_collision` warning class exists for
exactly this shape. Both are affected by the phase-3 streaming release that
site 12 measured: `source_contents_owner` is emptied by
`reclaim_streaming_source_contents_owner()` and `ctx.sources[].content` by
`evict_sources()`, both at `driver_hir_pipeline_lowering.spl:497-506`.

**Blast radius is a cache MISS, not a hard failure.** :1761 only decides
whether a cached object may be reused; a released content yields `""`,
`source_snapshot_matches` goes false and the witness reason becomes
`source-mutated-since-parse`, so the module is simply rebuilt. That is why
site 12 surfaced at capsule freeze and not here.

**Fix shape (not done here):** delete one definition — name the surviving one
for the carrier it reads — and, if the surviving one must answer after a
streaming release, route it through the same fail-closed recovery site 12
added (`CompileContext.frozen_native_source_identity_at_v1`), so a released
content re-reads disk only when the bytes still hash to the load-time capture.
