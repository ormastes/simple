# Stage4 process provider

Mirror of `test/01_unit/compiler/backend/stage4_process_provider_spec.spl`.

The executable SSpec verifies the exact hosted process ABI, tuple-facade mapping, FreeBSD `closefrom` gating, POSIX and Windows owner selection, and provider inventory, projection, and cleanup.

It is source/build-contract evidence and does not launch subprocesses on every supported host.
