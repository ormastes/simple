# FreeBSD `simple-native-all` test link: duplicate atomic-write symbol

## Failure evidence

On release source `96c901e0130d3dd4f6d2528e47532e040ff6ef7e`, [FreeBSD job 109192601284](https://github.com/ormastes/simple/actions/runs/36501285141/job/109192601284) completed the `simple-driver` bootstrap-profile build in 9m 17s. With Cargo build jobs and test threads both bounded to one, `cargo test --workspace --lib` progressed to linking the `simple-native-all` library test, then exited 101. FreeBSD `ld` reported duplicate `rt_file_atomic_write` definitions from `native_all/src/lib.rs:1164` and the bundled `simple-runtime` `file_ops.rs:428`. The retained local job log is `build/bsd-ci/current-freebsd-job.log`, SHA-256 `47439d318513b60ab5c6851890a0db1f3b7a40e8e04ce3bdf131cc7285b426f3`.

This terminal result is a source link error, not the earlier SIGKILL. The prepared FreeBSD `CARGO_PROFILE_TEST_DEBUG=0` candidate was discarded.

## Fix

`simple-native-all` already reexports `simple-runtime`, which owns the `#[no_mangle]` atomic-write entrypoint. Remove the extra native-all shim and its private duplicate implementation. Keep atomic-write behavior assertions with the runtime tests, including replacement, mode `0o4740` preservation, missing parents, empty path rejection, and failure without temp residue when the target is a directory. Make the Rust runtime remove the temp file and return failure if permission preservation fails, matching the C runtime's fail-closed `fchmod` handling.

The other apparent Rust extern-name overlaps in `native_all` are feature-complementary (`driver-compat` versus `driver-hooks`, and Vulkan versus no Vulkan); this report addresses only the unconditional symbol collision.

## Qualification

The focused `simple-runtime` atomic-write tests passed on the Linux aarch64 host (2/2), and the changed special-mode assertion passed again after restoring `0o4740`. The bounded local `simple-native-all --lib` test linked and passed 11/11 tests. The private logs are `build/bsd-ci/runtime-atomic-tests.log`, `build/bsd-ci/runtime-atomic-mode-test.log`, and `build/bsd-ci/native-all-lib-tests.log`. A new source-matched FreeBSD CI job is still required to prove this link on FreeBSD. This fix does not qualify the full QEMU bootstrap.
