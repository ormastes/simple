# SimpleOS toolchain payload runtime link remains unverified

Status: open. The x86_64 SimpleOS sysroot builds, but the existing target
toolchain producer cannot link `/usr/bin/simple`; no guest bootstrap claim is
supported by this attempt.

Reproduction from a clean checkout after building the sysroot:

```sh
sh src/os/port/llvm/sysroot.shs
SEED=/path/to/bootstrap/simple taskset -c 7-13 \
  sh scripts/ci/build-simpleos-toolchain.shs --only x86_64
```

The final `ld.lld` output reports exactly nine undefined symbols:
`rt_is_debug_mode_enabled`, `spl_thread_cpu_count`, `rt_getpid`,
`sched_yield`, `rt_thread_sleep`, `spl_panic`, `spl_strdup`, `rt_is_dir`,
and `spl_str_concat`. A source correction adds the target-compatible
`runtime_legacy_core.c` object, SimpleOS `sched_yield`, and SimpleOS-specific
sleep/debug-mode implementations. A focused cross-compile and `nm` check
confirmed all nine symbols are defined. The payload has not been relinked
after this correction, so this bug stays open pending a fresh target build and
guest execution.

The isolated attempt and exact final linker output are retained at
`/tmp/simpleos-bootstrap-lane-20260922/build/ci/simpleos_toolchain/x86_64-unknown-simpleos/build.log`
(SHA-256 `8b0dcacc686cdada99e8ce48c1ef9caf9f1f1aae943a3984de7aa15e83337f67`).
The wrapper transcript is
`/tmp/simpleos-bootstrap-lane-20260922/build/simpleos-toolchain-build-native-final.log`
(SHA-256 `428bf233b8a09ec843fe86ac3c2a14692a814b02ba4b7c7ebfb5ac8726dfaea7`).
The successful sysroot build transcript is
`/tmp/simpleos-bootstrap-lane-20260922/build/simpleos-sysroot-build.log`
(SHA-256 `d567890d94295de3c87d76e9c71d7416a641ce7e0a24cbff6030f0ed6ccdf8db`).

The existing `scripts/check/check-simpleos-compiler-filesystem-qemu.shs`
separately reports that the production in-guest compiler workflow is not
wired. The existing UEFI SSH hello lane cannot start without the target payload
and a bootable kernel artifact in this isolated checkout.
