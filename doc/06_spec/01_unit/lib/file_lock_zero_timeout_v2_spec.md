# Actual legacy POSIX lock trylock parity

Source: `src/runtime/test/runtime_file_lock_zero_timeout_v2_test.c`.
Evidence: **NOT_RUN**, including link/profile qualification. No compiler or
native test slot was requested or used. This is an authored source manual.

The eventual native runner must link the actual legacy runtime.c/platform
provider and exclude all strong rt_file_lock twins: runtime_native.c,
runtime_host_file_exports.c and Rust. A result from a strong twin does not
exercise this fix and cannot be admitted as legacy-provider evidence. The
current stale two-word platform harness is not used or repaired here.

1. Acquire a real temporary-file lock with the public three-word ABI and a zero
   timeout. Require an actual nonnegative owner handle.
2. While the parent retains that lock, fork a child that calls the actual API
   with timeout zero. Require -1 through a pipe and successful child exit.
   A three-second alarm converts a blocking LOCK_EX regression into failure.
3. Repeat the same contention prevention with a negative timeout, exercising
   the same documented nonpositive single-attempt branch.
4. Release the original owner and require another actual successful zero-timeout
   acquire/release before removing the fixture.

These cases neither invoke a service action nor establish owner-bearing cleanup
for the raw legacy API. The alarm is a regression bound, not a measured latency
or event-loop performance qualification.
