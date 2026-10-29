# Darwin ASan initialization reenters malloc before test entry

Observed on 2026-10-29 while validating authenticated Mach-O provisioning on
Darwin 25.5.0 arm64. Compiling the small signature selfcheck with Clang
`-O1 -g -fsanitize=address,undefined` produced an executable that consumed CPU
without reaching `main` or creating its output fixture.

A native process sample showed this cycle:
`libSystem_initializer -> __malloc_init -> wrap_malloc_default_zone ->
AsanInitInternal -> InitializeShadowMemory -> MemoryRangeIsAvailable ->
get_dyld_hdr -> dyld_shared_cache_iterate_text_swift -> _Block_copy -> malloc ->
AsanInitFromRtl -> StaticSpinMutex::LockSlow`.

The owned test process was terminated and reaped. No ASan pass is claimed.
The same authenticated malformed-input matrix and provisioned native launch
passed with `-fsanitize=undefined` alone. Native owner/worker adversarial checks
also passed. This report records a host-toolchain validation gap; it does not
attribute the initialization failure to the image parser.

Resume by qualifying an ASan runtime against this OS build, then run
`rt_sosix_darwin_signature_selfcheck.c` against a normal thin native fixture.
Do not leave an unbounded sanitizer initialization process running.
