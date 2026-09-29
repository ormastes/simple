# Stage4 positional AOT repeats work after successful no-op publication

- **Status:** Diagnosed — expected refusal for an unadmitted Stage4 compiler
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 standalone compiler
- **Impact:** repeated identical AOT requests still parse, compile, and link

After the source-owner text copy fix, hello AOT returned exit 0 and the
native no-op receipt publisher did not reject the build. An immediately
repeated invocation with the same source, flags, output path, compiler binary,
and environment also returned exit 0, but did not print the
`[MBH-NFR-002] admission=hit` receipt. Its log shows load/parse/MIR/native
compile/link work and a 576 ms build, versus 635 ms for the first request.
The second request is therefore not an admitted no-op cache hit.

The 2026-09-29 trace showed `current-missing` on both invocations. The first
publication returned `ok`, and its 64-byte `CURRENT` file existed. The second
invocation used a different request identity, so it looked under a different
`CURRENT` path. `native_build_compiler_identity()` deliberately includes PID and
time when `SIMPLE_ABI_POLICY` or `SIMPLE_ABI_ADMISSION_RECEIPT` is absent. Both
were absent in this standalone Stage4 invocation. The differing keys are the
intended fail-closed behavior for an unadmitted compiler, not a broken pointer
write or a source/output fingerprint mismatch. Do not remove the ABI admission
check to make this diagnostic build hit.

**Next:** run the native no-op performance proof with a compiler that has a
valid, matching Stage-2 ABI admission receipt. If that run misses, record its
attributed reason and repair that specific mismatch. This standalone Stage4
measurement cannot prove the Target 6 warm-admission goal.

Evidence: `build/mini_builds/target5_stage4_owner_substr_hello.log` and
`target5_stage4_owner_substr_noop_hit.log`.
