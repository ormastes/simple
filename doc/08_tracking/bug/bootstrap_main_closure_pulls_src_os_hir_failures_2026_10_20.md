# bootstrap_main's source closure pulls src/os; 21-23 os modules fail HIR (Stage 3 and compiler_cli_build)

- Status: OPEN (edge being traced)
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
