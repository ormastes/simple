# bootstrap_main's source closure pulls src/os; 21-23 os modules fail HIR (Stage 3 and compiler_cli_build)

- Status: FIX PROPOSED (resolver; see Cause)
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P0 (blocks Stage 3 on release_phase3)

## Observation

Stage 3 resumed from bootstrap-r16b (Stage 2 sha256 645e62a815d0..., tree
f9527544c50 + the capsule fix), sharded route, 8 workers:

- source closure 2280 modules (bootstrap-r14 on 630f773bdc7: 1316). The new
  modules include ~460 `os.*` (os.apps 91, os.services 79, os.kernel 67,
  os.tools 54, os.drivers 52, os.compositor 33, ...), plus lib.common (151),
  lib.gc_async_mut (140), lib.nogc_sync_mut (85).
- HIR: `completed_workers=1 failed_workers=7 failed_modules=21`, then
  `error: HIR aggregate failure; final worker and artifact publication blocked`
  after 529 s. All 21 failures are src/os modules, e.g.
  `src/os/mod.spl: unresolved type: DisplayMode`,
  `src/os/apps/sshd/ssh_session_channel.spl: unresolved name: rt_bytes_u8_at`,
  src/os/compositor/fb_backend.spl:148, src/os/crypto/aes128_gcm.spl:303.
- The Stage 2 matrix's compiler_cli_build fails the same way
  (`failed_workers=8 failed_modules=23`).


## Cause

Traced with a diagnostic Stage 2 relink that logs every closure edge
(`phase1:load_sources:closure:edge`). The Stage 3 coordinator's own walk
(no source roots) closes over 1352 modules. The HIR shard workers walk with
the snapshot source roots from `native_build_snapshot_source_roots_v1`
(src/app/io/_CliCompile/native_build_snapshot_roots.spl), whose default list
gained `src/os` in the Phase 4 root-handoff change (44bfe296d79). There the
single edge into src/os is

```
closure:edge to=mod input=mod file=src/os/mod.spl from=src/compiler/55.borrow/borrow_check/__init__.spl
```

`borrow_check/__init__.spl` re-exports `... from mod` (its sibling mod.spl,
spelled bare since 74e5c62f59f). `_driver_resolve_source_root_entry_import_from_v1`
probes every source root before the importer's directory, so the bare `mod`
matched `<snapshot>/src/os/mod.spl`, and src/os/mod.spl imports every os
package. The root-less walk falls through to the checkout resolver, which
tries the importer's directory and finds borrow_check/mod.spl.

src/lib/common/ui/window_scene_draw_ir.spl:59 (`use os.compositor.display_backend_core`)
is not on the path from bootstrap_main: it is only reached from inside src/os.

## Fix

For an undotted name that the checkout resolver resolves from the
importer's directory, the source-root resolver reports Missing so the walker
uses the checkout resolver, the same answer as the root-less walk. Spec:
test/01_unit/compiler/driver/source_root_doubled_package_import_spec.spl
(`mod -> src/os/mod.spl` before, `borrow_check/mod.spl` after).
