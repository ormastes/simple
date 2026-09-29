# Stage4 positional AOT repeats work after successful no-op publication

- **Status:** Open
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 standalone compiler
- **Impact:** repeated identical AOT requests still parse, compile, and link

After the source-owner text copy fix, hello AOT returned exit 0 and the
native no-op receipt publisher did not reject the build. An immediately
repeated invocation with the same source, flags, output path, compiler binary,
and environment also returned exit 0, but did not print the
`[MBH-NFR-002] admission=hit` receipt. Its log shows load/parse/MIR/native
compile/link work and a 576 ms build, versus 635 ms for the first request.
The second request is therefore not an admitted no-op cache hit.

**Next:** expose the exact `native_noop_admit_v1` miss reason and compare the
request identity, `CURRENT`, authenticated receipt, source fingerprint, and
output fingerprint across the two invocations. Repair the mismatch without
waiving source or output authentication. This is a compile-performance TODO
for Target 6 as well as a Stage4 cache bug.

Evidence: `build/mini_builds/target5_stage4_owner_substr_hello.log` and
`target5_stage4_owner_substr_noop_hit.log`.
