# Managed SimpleOS container launch calls a removed loader entry

Status: repaired in source (2026-11-05); host-side executable verification is
blocked by two toolchain evidence blockers tracked at
`seed_cfg_strip_kernel_closure_undefined_externs_2026-11-05.md` and
`seed_interpreter_cross_module_struct_field_read_zero_2026-11-05.md`
(no admitted self-hosted CLI on this host; seed-run verdicts are
diagnostic-only). Priority: P1. Owner: SimpleOS authenticated loader and
managed workload.

Repair landed:
- `src/os/kernel/loader/managed_image_authority_v1.spl` (new): stages the
  caller-verified image bytes into a loader-private ramfs mount, builds the
  `ExecutableImageHandleV1` from the staged binding's exact
  mount/file/generation identity plus the ELF authenticated layout, and
  issues the one-use token through `executable_authority_issue_verified`.
  No pathname, caller identity, or byte vector alone can mint authority.
- `src/os/kernel/loader/managed_workload_launch.spl`: re-routed through the
  new staging module + `fs_exec_adopt_authenticated_with_launch_v1`
  (APP_LAUNCHER recipe), preserving the SpawnSpec self-consistency check and
  re-adding the exact-bytes-vs-`spawn_spec.image_hash` check that the removed
  path used to perform; resource/cpu/syscall/filesystem binding is unchanged.
- `src/os/kernel/loader/root_service_catalog.spl`: re-routed through the same
  staging module + `scheduler.adopt_authenticated_executable_pid_with_launch_v1`,
  minting the child CSpace from the catalog's own SpawnSpec under the
  unchanged `has_root_mint_authority` gate, preserving exact catalog grants
  (including device leases).
- `src/lib/nogc_async_mut/fs_driver/mount_table.spl`: `positioned_read_bytes`
  / `positioned_write_bytes` are now `pub me` (binary-exact I/O was
  module-private; ramfs already stores `[u8]` natively).
- `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl`: updated
  to the authenticated seam (registry fixture, page-aligned ELF, per-attempt
  token independence, bytes-mismatch rejection); job-shape expectations that
  belonged to the old CSpace mint were dropped.

Historical record of the original defect:
`src/os/kernel/loader/managed_workload_launch.spl` imported and called
`fs_exec_register_image_with_spawn_spec`, but
`src/os/kernel/loader/fs_exec_spawn.spl` has no such definition. The root
service catalog also imports that missing entry. The current authenticated
route is `fs_exec_adopt_authenticated_v1`, which consumes a loader-issued
registry token; a path, image bytes, or kernel caller identity cannot mint
that token. This mismatch blocks a source-matched build of the real
`SimpleOsContainerProviderV1` scheduler launch path.

Repair the managed workload and root-service callers through the loader's
authenticated image registry and one-use token, preserving the SpawnSpec,
policy digest, filesystem view, resource limits, and caller authority checks.
Do not recreate the removed path-only mint as a compatibility shim.

Acceptance: a source-matched Simple check resolves every loader symbol; a
focused SimpleOS test launches one policy-approved image into the kernel
scheduler, observes its assigned task ID and actual exit via the arm64
authenticated FS-exec handoff, and rejects wrong/replayed tokens, mismatched
image or policy, missing task, and stale exit. Run the live macOS QEMU guest
fixture with the pinned image and preserve boot, task-exit, and teardown
receipts. The current Mac host lacks that image, so this issue remains open.
