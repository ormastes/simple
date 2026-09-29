# SimpleOS secure server lifecycle

**Status:** PARTIAL/RED — executable policy scenarios pin both canonical
filesystem paths and prove metadata alone is not staging, while unregistered/PID-zero execution and missing
socket capability cannot promote an artifact to runnable. The positive receipt
used by that policy scenario is constructed test data, not live execution
evidence.
The policy distinguishes a live listener from a completed process and binds
artifact/image hashes, boot-local launch ID, scheduler-owned PID, observed
start, and nonce socket exchange. This is a correlation contract only; the
fixture does not claim a QEMU launch or socket success.
Executable build/staging, live QEMU socket, restart, and artifact-hash oracles
remain unresolved.

The intended live scenario flow is to build and stage release-native web and database server artifacts, boot SimpleOS, launch each artifact through the filesystem execution path, exchange a request over its bound socket, drain it cleanly, restart the OS, and verify committed database state. Required evidence is typed `binary`, `exec`, `protocol`, `log`, and `artifact` output under the mirrored test-artifact path.

The remaining live scaffold fails explicitly rather than accepting rootfs
presence, linked-in calls, or synthetic transcripts as execution proof.

**Executable SPipe:** `test/03_system/app/server_platform/feature/simpleos_server_lifecycle_spec.spl`
