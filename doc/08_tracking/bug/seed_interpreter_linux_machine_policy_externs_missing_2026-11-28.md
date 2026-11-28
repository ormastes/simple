# Linux machine-policy libc externs unknown to the seed interpreter

- id: seed_interpreter_linux_machine_policy_externs_missing_2026-11-28
- status: open (seed side); no workaround (the spec observes the real process)
- component: seed interpreter (`src/compiler_rust/compiler/src/interpreter_extern/posix_abi.rs`)
- found by: `test/03_system/tools/linux_service_native_identity_v3_spec.spl` under the Rust seed

## Symptom
Rust seed interpreter, diagnostic (2026-11-28): `executed=4 passed=0 failed=3 blocked=1`.
Example 1 fails with
`semantic: test/03_system/tools/linux_service_native_identity_v3_spec.spl:70:5: unknown extern function: gettid`.
The FILE is misattributed (the seed names the entry spec); the real site is
`src/lib/nogc_sync_mut/io/linux_machine_process_origin_v1.spl:70:5`
(`val tid = gettid() as i64`). Examples 2 and 3 then fail with
`service-identity-fixture-prior-pair-unresolved`: the fixture quarantines after the
first failure by design, so they share the one root cause. Example 4 is the
host.sdn-gated `pending` (no `serviceInstallFixtureParent`), unrelated.

## Root cause
`src/lib/nogc_sync_mut/io/linux_machine_policy_abi_v1.spl` declares Linux libc externs
`getuid`, `getgid`, `getegid`, `gettid`, `getpid`, `readlinkat`, `fstatfs`, `ioctl`,
`sysconf`. The seed's `posix_abi.rs` registers only `COMMON_NAMES`
(`malloc`, `free`, `realpath`, `readlink`, `open`, `read`, `pread`, `write`, `close`,
`fsync`) plus `LINUX_NAMES` (`statx`, `openat`, `geteuid`). None of the nine names
above is registered. `getpid` appears to work only because same-named Simple
functions exist (`src/lib/nogc_sync_mut/io/sysinfo_ops.spl:36`, `io_runtime.spl:566`)
and win the co-compiled name collision; `gettid` has no such twin and fails.

This is not drift from the host.sdn move (#12334 / `fbc2390c77f`): that change only
touched example 4's gate; examples 1-3 never had an environment precondition.

## Seed fix (not done here)
Add the nine names to `LINUX_NAMES` / `is_supported_name` and the dispatch match in
`posix_abi.rs` (calling `libc::gettid`, `libc::getuid`, ... with the declared
argument shapes), with drift tests in `extern_drift_tests.rs`. The pure-Simple
self-hosted binary is the real target for this system spec.
