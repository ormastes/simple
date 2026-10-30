# Aspect/MC-DC loader owner modules missing on release/1.0.0 after transplant

Status: open. The specs are marked `@tag:in-development` until the owners land.
Found by: the Lunar loader sweep, 2026-10-30.

## Symptom

```
cannot resolve import: module path segment `compiler` not found   (E1034)
```

for these specs (each fails the same way when run alone, so the cause is not the
directory-run search roots):

- `test/01_unit/compiler/loader/aspect_loader_integration_spec.spl` -> `compiler.loader.aspect_acquisition`
- `test/01_unit/compiler/loader/mcdc_aspect_binding_spec.spl` -> `compiler.loader.mcdc_aspect_binding`
- `test/01_unit/compiler/loader/mcdc_aspect_pack_payload_spec.spl` -> `compiler.loader.mcdc_aspect_pack_payload`

The message names only the first path segment. The real failure is that the leaf module does not exist.

## Root cause

The transplant `88aac2ffe28` (2026-09-29) carried the specs onto release/1.0.0
but not the owners. The owners exist only on `origin/chore/merge-share-history`
(`a8244005f9b`, `src/compiler/99.loader/`).

## Why the owners were not just restored

Restoring the three files byte-identical was tried. The import errors went away,
but the next layer is also missing on release:

- `std.nogc_sync_mut.io.coverage_mcdc` (223 lines, share-history only)
- `McdcPolicy.StaticOff` / `StaticOn` (`compiler.common.config`). Release has the
  same variants as `McdcMode` in `src/lib/common/mcdc/model.spl`, imported by
  `config.spl:7`, so this item is an import rename, not a feature port.
  `mcdc_aspect_pack_payload.spl:374,379` also uses `McdcPolicy.Dynamic`, which
  maps to `McdcMode.DynamicAspect`. `McdcPolicy.Invalid` and its helper
  methods have no `McdcMode` equivalent, and the owners do not use them.
- `pack_index_cached_count` (`compiler.loader.aspect_pack_index_cache`)

Measured with the owners restored: aspect_loader_integration 0/1,
mcdc_aspect_binding 0 examples run, mcdc_aspect_pack_payload 2/4.

Those dependencies live in files that release has since moved past
(`src/lib/common/aspect_pack.spl` and `src/compiler/00.common/config.spl`,
the latest being `398a1232eb3`, 2026-10-21). On those files the two trees differ
by about 1,500 lines, so copying the share-history versions would roll back
newer release work. The port has to be a reviewed merge of the MC-DC aspect
feature onto the current release owners.

## To close

1. Port `coverage_mcdc` and `pack_index_cached_count` onto the current release
   owners, without reverting `398a1232eb3`. Rewrite the `McdcPolicy` uses in
   the restored owners and in `mcdc_aspect_pack_payload_spec.spl` to release's
   `McdcMode`.
2. Restore the three `99.loader` owners from `a8244005f9b`.
3. Remove `@tag:in-development` from the three specs and run them one file at a time.
