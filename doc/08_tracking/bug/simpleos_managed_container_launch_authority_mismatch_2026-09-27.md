# Managed SimpleOS container launch calls a removed loader entry

Status: open. Priority: P1. Owner: SimpleOS authenticated loader and managed workload.

`src/os/kernel/loader/managed_workload_launch.spl` imports and calls
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
