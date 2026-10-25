# Stage 2 positional native-build fails to restore optional text environment

Status: explicit payload-unwrapping workaround applied in the positional cache
and output-mode restore helpers. Native Stage 2 confirmation is pending the
combined candidate after the enum-wire lane is committed.

## Failure evidence

On release_phase3 merge `3165efd1342804b49dac0c1a28f499aae5171f04`, candidate
`/tmp/enum-wire-carrier-rebuild-20261025/simple` (SHA-256
`5fa94dda2a04dccb6a346907b0d7842699bb29d5b585f227d1232109e48f0f1f`) compiled
and linked the positional Hello fixture, then returned exit 1 with
`could not restore native-build cache environment`. The generated executable
ran successfully and printed `hello` (exit 0). The invocation used an explicit
`--cache-dir`, so the prior cache value was present while the positional route
temporarily rebound it.

The restored source helpers used `if previous == nil` followed by passing
`previous` directly to `sosix_env_set`. A native producer can retain the
optional box instead of narrowing its payload. This is the text-valued instance
of `optional_array_payload_narrowing_native_2026_10_21`.

## Repair and acceptance

Both restore helpers now pattern-bind `if val present = previous` before the
setter call. The absent branch still removes the variable, preserving the
difference between absent and an explicitly empty value. The focused cache
binding spec exercises present nonempty, present empty, and absent snapshots
through the real SOSIX environment functions.

Acceptance requires the focused spec and the exact positional Hello native
build/run to pass under the combined candidate. The pre-fix Hello evidence is
preserved in `/tmp/enum-wire-carrier-rebuild-20261025/hello/`; no post-fix
native verification is claimed by this change.
