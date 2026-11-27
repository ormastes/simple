# bootstrap_main's source closure pulls src/os; 21-23 os modules fail HIR (Stage 3 and compiler_cli_build)

- Status: FIXED (closure edge); src/os name gaps listed below remain open
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

The only non-os closure module importing `os.*` is
src/lib/common/ui/window_scene_draw_ir.spl:59
(`use os.compositor.display_backend_core`); the edge from the old closure
into the new modules is still being traced.

## Root cause (traced 2026-10-20, macOS Stage 3 log, same 2280/21 shape)

The edge is not an `os.*` import. `src/compiler/55.borrow/borrow_check/__init__.spl:30-33`
re-exports `... from mod`. The parser treats a bare export source as the
package sibling `.mod` (`parse_export_source_module`,
`10.frontend/core/parser_decls_use.spl:110-111`), but the closure import
extractor (`_driver_entry_import_module_paths_text_fallback`,
`80.driver/driver_source_loading.spl`) collected it BARE as `mod`.
`_driver_resolve_source_root_entry_import_from_v1` then probed every snapshot
root for `<root>/mod.spl`; `src/os` is a root (`native_build_snapshot_roots.spl`,
c9bf7cf1440) and owns a top-level `mod.spl`, so `mod` bound to
`src/os/mod.spl`, which imports every `os.*` subsystem. Reproduced with a BFS
over the resolver: `borrow_check/__init__.spl imports mod -> src/os/mod.spl`.

Trigger: 4eb4691d72a (landed on release_phase3 via #3803 / 9118b9e457e,
after the 1316-module r14 tree 630f773bdc7) flipped package resolution to
prefer `__init__.spl` over `mod.spl`, so `compiler.borrow.borrow_check.*`
began scanning the `__init__` facade and its `from mod` lines (74e5c62f59f)
for the first time.

Fix: the extractor emits a bare `export ... from X` as `.X`, matching the
parser. BFS reproduction: 2499 files / 712 os -> 1331 files / 0 os.

## src/os names that stay unresolved on their own (not fixed here)

Defined nowhere under src/: `SurfaceDesc`, `DisplayMode`, `noalloc_log_debug`,
`_host_gpu_submit_draw_ir_common`, `spawn_binary_with_args`,
`execute_scene_to_buffer`, `draw_text_shadow`, `FbCompositorBackend`.
`src/os/crypto/aes128_gcm.spl:303,362,365` call `_inc32`/`_make_j0`, but the
file defines `_aes128_gcm_inc32`/`_aes128_gcm_make_j0` (256, 322).
Defined elsewhere but not imported by the failing file: `mmio_read*`,
`log_raw_println`, `_bytes_to_hex`, `rt_bytes_u8_at`, `unsafe_addr_of`,
`Scheduler*EvidenceV1`, `rt_thread_sleep`, `readdir`.

Revalidated 2026-11-02: still plausible because doc itself lists remaining src/os name gaps after the closure-edge fix.

## Verification (2026-11-02, opf-6)

Checked against origin/release/1.0.0 at 807253b2748. Result: FIXED (closure edge).

- `src/os` and `src/package_ownership` still exist on release/1.0.0 (`git ls-tree`).
  The coordinator's "paths removed" premise is wrong, so this bug is not stale
  for that reason. It is fixed in source instead.
- Fix: e9505f50f94 "collect bare `export X from M` as the sibling `.M`".
  Carried into the split-out closure core by 98519d733d6. Current code: `src/compiler/80.driver/driver_entry_closure_core.spl:787-788`
  (`if tail != "" and not tail.contains("."): tail = "." + tail`).
- Trigger removed too: `src/compiler/55.borrow/borrow_check/__init__.spl` no
  longer has `from mod` re-exports.
- Regression specs: `test/01_unit/compiler/bootstrap/entry_closure_from_import_spec.spl:37`
  and `test/01_unit/compiler/bootstrap/closure_walk_parity_spec.spl:54-55`
  (bare `export BorrowChecker from mod` must never bind `src/os/mod.spl`).
- No compiler closure root or launcher references `src/os` (only comments in
  10.frontend). The remaining `src/os` references are in os/firmware build
  scripts and SFFI audits, which are not part of the bootstrap_main closure.
- Not re-run here (no heavy build). The src/os unresolved-name gaps listed above
  are outside this bug's closure-edge scope.
