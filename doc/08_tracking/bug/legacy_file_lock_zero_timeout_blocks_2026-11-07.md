# Legacy POSIX file lock blocks for a zero timeout

Severity: P1. One-line source repair; native prevention test **NOT_RUN**.

`runtime_native.c` makes a nonblocking LOCK_EX|LOCK_NB attempt when timeout is
nonpositive. The legacy `runtime.c` provider's actual `platform/unix_common.h`
branch instead used blocking LOCK_EX. A caller requesting a trylock could
therefore block its event loop while a different writer retained the lock.

The legacy branch now uses LOCK_EX|LOCK_NB. The positive-timeout poll path,
public `(path_ptr, path_len, timeout_secs)` ABI, lock namespace and legacy
unlock behavior remain unchanged. This is raw API parity, not a claim that
legacy callers now have typed owner-bearing cleanup or universal journal
closure.

The standalone prevention source exercises actual uncontended acquire/release,
real cross-process contention for zero and negative timeouts, and acquisition
after the original owner releases. A pipe carries the child result while the
parent retains the real lock. An alarm turns the blocking regression into a
bounded failure instead of a hang. It does not report measured latency.

Qualification requires linking the actual legacy runtime.c/platform provider,
excluding runtime_native.c, runtime_host_file_exports.c and Rust's strong twin.
Linking the strong implementation would mask this bug and cannot qualify this
repair. No current driver/link profile was executed. Related existing harness
ABI drift is recorded separately in
[legacy platform test ABI drift](legacy_platform_lock_test_abi_drift_2026-11-07.md).
