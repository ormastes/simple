# Graphics 2D showcase nil-receiver crash
## Triage 2026-11-25 — ledger index records closed 2026-08-17; runtime confirmation environment-blocked here

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Triage 2026-11-25 (work/p2w2-aa-20261125): the ledger index
(`doc/08_tracking/bug/recent_bugs.md` line 1027) records this bug as
**closed 2026-08-17**, but this doc's own body was never updated and still
says Open. Runtime confirmation is not possible from this Windows host: the
repro (`bin/simple run examples/06_io/ui/graphics_2d_showcase.spl`, file
present at HEAD `8aa26f51e72`) requires the self-hosted binary (the pinned
tracked Rust seed cannot load `src/lib` at HEAD — it rejects the
`@representation_boundary` decorator) and a display/present path for the GUI
acceptance legs. Left un-merged with the index: treat as closed per
`recent_bugs.md` unless a fresh headless run on a self-hosted binary
reproduces the `field access on nil receiver` trap; if it does, reopen with
that evidence.

## Status

Open. Blocks `graphics_2d_showcase` standalone readiness.

## Reproduction

```text
bin/simple run examples/06_io/ui/graphics_2d_showcase.spl
runtime error: field access on nil receiver
exit=132
```

The failure occurs before the first Engine2D readback/provenance row. The app no longer reads argv or environment state; the first application call is `Engine2D.create_offscreen(800, 600)`. Source review found concrete backends were boxed into `Engine2D.backend` and then dereferenced again for capability/name fields. Those values are now precomputed before boxing, but the deployed self-host still traps. The same exit occurs in the existing `engine2d_backend_test.spl`, so this is a shared Engine2D/self-host trait-boxing blocker rather than showcase-only logic. The runtime provides no source stack. Catalog readiness remains false.

## Acceptance

- Headless software execution prints backend, readback source, checksum, nonzero count, dimensions, and pixel count.
- The frame is 800x600 and nonblank.
- Requested GPU backends must match the actual backend and report device-readback provenance with a positive real handle or fail explicitly.
- Five semantic scene samples must demonstrate at least four adjacent differences; background-only output fails.
- GUI mode creates a real window and routes close/Q/Escape without reporting unavailable presentation as success.

