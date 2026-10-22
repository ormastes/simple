# phase-C cli row: 30 of 33 hir-fatal modules are seed-failing source gaps, not self-hosted parity

Date: 2026-10-20
Row: stage2-compiler-tests `compiler_cli_build` (scv snapshot 877ee1df, self-hosted candidate dce90daba)
Log: `.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/compiler_cli_build.log`

## Summary

The v35 chain reached "HIR 3247/3280" on the cli row; 33 modules failed with
`[hir-fatal]`. Triage (run each module through the Rust seed from the snapshot
root, `seed compile <module> --format=smf`) split them:

- **3 modules pass under the seed and failed only under the self-hosted
  frontend** — TRUE parity gaps, fixed in this cycle (see the commit on
  `fix/v35-hir-reexport-runtime-authority`): import-tolerance for selective
  imports of names a facade does not export, and closure-wide visibility via
  the ungated unique-owner fallback (`try_register_bootstrap_global_symbol`).
  - `src/compiler/90.tools/header_gen/__init__.spl`
  - `src/os/userlib/net.spl`
  - `src/os/services/nvfs/__init__.spl`
- **30 modules fail under the SEED TOO** — upstream-owned source bugs in the
  os/app layers. The self-hosted compiler now fails them with the same
  attributed use-site errors as the seed would (after the parity fixes); the
  row cannot reach 3280/3280 until the sources are fixed.

## Seed-failing modules and their seed errors (first error per module)

| Module | Seed error (family) |
|---|---|
| src/app/io/__init__.spl | bootstrap-registry symbol (`_promote_bootstrap_registry`) |
| src/app/io/feature_registry.spl | interpreter-required constructs (14 fns) |
| src/compiler/80.driver/driver_api_project_build.spl | bootstrap-registry symbol |
| src/os/apps/sshd/ssh_session_channel.spl | undefined identifier: `_inc32` |
| src/os/apps/sshd/ssh_session_kex.spl | undefined identifier: `_inc32` |
| src/os/compositor/browser_backend.spl | undefined identifier: `METAL_FONT_PACKED_MAX_WORDS` |
| src/os/compositor/fb_backend.spl | interpreter-required constructs (18 fns) |
| src/os/compositor/mod.spl | undefined identifier: `METAL_FONT_PACKED_MAX_WORDS` |
| src/os/compositor/window_effects.spl | struct 'ANY' field 'width' |
| src/os/crypto/aes128_gcm.spl | undefined identifier: `_inc32` (defines `_aes128_gcm_inc32`, calls `_inc32`) |
| src/os/desktop/shell.spl | undefined identifier: `METAL_FONT_PACKED_MAX_WORDS` |
| src/os/desktop/shell_types.spl | `_namespace_finish` unavailable |
| src/os/kernel/net/rt_net_socket_facade.spl | interpreter-required constructs (12 fns) |
| src/os/lib/gpu_bridge/host_gpu_ivshmem.spl | `_host_gpu_submit_draw_ir_common` |
| src/os/mod.spl | undefined identifier: `DisplayMode` |
| src/os/services/display/display_service.spl | undefined identifier: `DisplayMode` |
| src/os/services/init/init_service.spl | interpreter-required constructs (2 fns) |
| src/os/services/mod.spl | undefined identifier: `DisplayMode` |
| src/os/services/netstack/_NetstackService/ipc_handlers.spl | codegen: relocation source section __const not executable code |
| src/os/services/nvfs/posix/__init__.spl | codegen body failure: `nvfs_posix_capabilities` |
| src/os/services/nvfs/posix/capabilities.spl | codegen body failure: `nvfs_posix_capabilities` (imports nonexistent `CapabilitySet` from std.fs_driver.capability; the struct lives in os.kernel.types.capability_types) |
| src/os/services/nvfs/posix/fs_driver_impl.spl | codegen body failure: `nvfs_posix_capabilities` |
| src/os/services/pm_service.spl | undefined identifier: `scheduler_execution_evidence_consume_once_v1` |
| src/os/services/vfs/mod.spl | `_namespace_finish` unavailable |
| src/os/services/wm/wm_codec.spl | undefined identifier: `unsafe_addr_of` |
| src/os/services/wm/wm_service_core.spl | `_namespace_finish` unavailable |
| src/os/services/wm/wm_service_protocol.spl | `_namespace_finish` unavailable |
| src/os/tools/pkg/pkg_manager.spl | `_namespace_finish` unavailable |
| src/os/userlib/_Window/client_methods.spl | struct `WmInputEvent` has no field `mouse_pos` |
| src/os/userlib/_Window/ipc_helpers.spl | struct `WmInputEvent` has no field `mouse_pos` |

## Required source fixes (upstream-owned)

1. `aes128_gcm.spl` (+ ssh_session_channel/kex): call sites use `_make_j0` /
   `_inc32`; the module defines `_aes128_gcm_make_j0` / `_aes128_gcm_inc32`.
   Rename one side.
2. `DisplayMode` / `DamageRect` / `SurfaceDesc` / `CapabilitySet` /
   `NetIfInfo`-style names are imported from facades that do not re-export
   them (or not imported at all); either fix the `use` lists or add the
   re-exports to the protocol modules (common.display_protocol.display_protocol,
   std.fs_driver facades).
3. `METAL_FONT_PACKED_MAX_WORDS`, `unsafe_addr_of`,
   `scheduler_execution_evidence_consume_once_v1`,
   `_host_gpu_submit_draw_ir_common`, `noalloc_log_debug`,
   `bytes_to_text`, `readdir`, `spawn_binary_with_args`, `draw_text_shadow`,
   `execute_scene_to_*`, `rt_bytes_u8_at`,
   `rt_net_last_ssh_plain_payload_len`, `NvmeBlockAdapter`, `HeaderGenerator`,
   `rt_cuda_*` / `rt_vulkan_*`, `process_run_inherit` / `rt_file_rename` /
   `rt_timestamp_now`: undefined identifiers — declare them or fix the
   importing call sites.
4. `WmInputEvent.mouse_pos`: field missing from the struct definition.
5. "interpreter-required constructs" modules (fb_backend, feature_registry,
   rt_net_socket_facade, init_service): native codegen gaps for constructs
   these bodies use — separate native-codegen work items.
6. `_namespace_finish` modules (shell_types, vfs/mod, wm_service_*,
   pkg_manager): the symbol is unavailable in the seed's compile of these
   modules — namespace-materialization gap, seed-owned.

## Self-hosted parity notes (fixed this cycle)

- Import of a name a facade does not export: seed SILENTLY tolerates
  (verified: import, annotation, even a call to a never-declared name
  compiles under the seed). The self-hosted frontend used to hard-fatal at
  registration ("module X has no exported item Y", hir-fatal, attributed to
  the importer); now downgraded to the existing
  `[hir-reexport-chase-unresolved]` receipt, use-site errors keep failing
  with correct attribution.
- Visibility: the seed resolves any name declared by exactly one module in
  the import closure from any importing module (flat global registry,
  transitive). The self-hosted restricted visibility to explicitly imported
  names; the unique-owner fallback
  (`try_register_bootstrap_global_symbol`) is no longer gated on
  SIMPLE_BOOTSTRAP=1 — the stage2/3 phase-C rows unset SIMPLE_BOOTSTRAP for
  tool invocations (dispatch hygiene) which had silently disabled it.
- Deliberate divergences kept: (a) a name with ZERO owners still hard-fails
  at its use site under the self-hosted frontend (the seed tolerates even
  that via dynamic dispatch — no row module needs it); (b) ambiguous names
  (multiple owners) give up rather than seed-style first-wins.
