# Interpreter MC/DC manifest contract

Executable specification:
`test/02_integration/app/test_runner/interpreter_mcdc_manifest_acceptance.spl`.
Requirement: REQ-MC-012. Status: AUTHORED_UNRUN.

The interpreter route must execute the authored example without a native
manifest prelude when MC/DC mode is `on` or `dynamic`. Four scenarios exercise
the real interpreter executor in isolated processes: static passing, static
failing, dynamic passing, and dynamic failing. The probe requires exactly one
executed example, the correct pass/fail counts, no manifest-contract panic,
and no fabricated MC/DC evidence. A failed authored expectation is an expected
probe observation, not a passing test substituted for the child verdict.

This harness is an explicit manual target: its filename contains neither
`_spec.` nor `_test.`, so normal directory discovery excludes it. Slow tests
run by default; slow classification does not provide the exclusion here.
Explicit execution requires a source-matched admitted self-hosted full CLI and SHA-256
in `SIMPLE_MCDC_TEST_RUNNER` and `SIMPLE_MCDC_TEST_RUNNER_SHA256`. Missing or
mismatched producer identity fails immediately; the spec does not build a
compiler or select a Rust seed. The probe receives mode and binary as CLI
arguments and sets its own environment, avoiding POSIX `env` or shell
dependencies and leaving the parent process unchanged. It explicitly asserts
that fork and coverage modes are disabled and authenticated example evidence
is enabled before running the child. No behavioral results are available yet.
The path/hash pin checks consistency only; the operator must establish actual
compiler admission and source compatibility independently before execution.
The pin is checked inside the probe before and after the runner call, the
resolved grandchild path must match it, and the parent checks the executor's
resolved-child diagnostic. This is not an admission-record verifier.

Both generated examples import `std.spec.*` so the framework can write
authenticated evidence. The expected red case additionally requires the
authenticated-assertion error classification and both unique actual/expected
text sentinel tokens, without assuming diagnostic case, order or formatting.
The child also writes a per-case marker from inside the authored example
before its assertion; the probe requires its exact mode/outcome identity.
A mere 0-pass/1-fail
transport, parse, missing-evidence, or budget error cannot satisfy the oracle.
The default-lane `interpreter_mcdc_verdict_spec.spl` exercises these negative
controls without spawning a compiler. Behavioral wrapper regression remains
an explicit acceptance target because it loads the real runner and children
and requires an independently admitted producer.

After independent producer admission, run `"$SIMPLE_MCDC_TEST_RUNNER" test
test/02_integration/app/test_runner/interpreter_mcdc_manifest_acceptance.spl
--mode=interpreter --assert-ran --timeout=1500` with the two pin variables set.
Use lowercase hexadecimal for the digest; comparison is exact. An explicit
`.spl` target is accepted even when its name is outside directory conventions.
Run from the repository root with a source-matched invoking CLI, so the outer
runner also contains this source repair. On Windows, supply the complete
existing `.exe` path as the pin rather than relying on extension inference.
The acceptance harness remains under `02_integration` for integration resource
classification even though its filename requires explicit selection.

Each scenario has a 300-second bounded capture and a 120-second inner child
limit; the spec declares a 1500-second outer allowance for all four scenarios.
These are execution bounds, not measured latency claims.

Native/coverage manifest authentication remains mandatory. Native missing-
manifest negative execution and the original Windows one-spec-directory CLI
reproduction remain required qualification beyond these focused executor
scenarios.
