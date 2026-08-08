# Stage 4 file facade uses parent instead of sibling-directory package

- **Status:** FIXED (focused; Stage 4 verification pending)
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02, provenance verification cycle 3
- **Area:** pure-Simple HIR module-surface export provenance

The first Stage 4 run with the refreshed provenance-aware Stage 3 failed fast
while resolving `std.nogc_sync_mut.io`'s plain `dir_create` export. A facade
file such as `io.spl` represents declarations in the adjacent `io/` directory,
so its canonical package root is `lib.nogc_sync_mut.io`. The resolver instead
dropped the final `io` segment and searched `lib.nogc_sync_mut`, where several
unrelated owners made the export appear ambiguous.

Plain-export resolution now tries the facade's own canonical module name when
that name has an indexed direct-child declaration, then falls back to the
ordinary parent package. `__init__` facades keep their existing package root,
and ordinary module facades without direct children keep parent-sibling
semantics. Focused exact and adjacent tests cover all three shapes.
