# Bootstrap platform handoff readiness

This manual verifies the checker contract for handing bootstrap work to
platform operators. It proves only that the checker self-test runs and that
the default report remains blocked until platform evidence exists. It does
not build Simple, launch a platform bootstrap, or claim platform acceptance.

The executable source is
`test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl`.
The shared flow helper is
`step_bootstrap_platform_handoff_readiness`.

## Preconditions

- Run from the repository root.
- The checker must be available at
  `scripts/check/check-bootstrap-platform-handoff-readiness.shs`.
- Platform bootstrap evidence is not assumed to exist.

## Scenario BPHR-001/BPHR-002: checker self-test claim boundary

1. Run the checker self-test:

   ```sh
   sh scripts/check/check-bootstrap-platform-handoff-readiness.shs --self-test
   ```

2. Require exit code `0`.
3. Confirm the output contains
   `bootstrap_handoff_self_test=pass`.
4. Confirm the output contains
   `platform_acceptance_claimed=false`.

The self-test is checker-contract evidence. Its `pass` marker does not mean
that any target platform has passed bootstrap.

## Scenario BPHR-003/BPHR-004: default blocked handoff

1. Run the checker with no mode flag:

   ```sh
   sh scripts/check/check-bootstrap-platform-handoff-readiness.shs
   ```

2. Require exit code `1` for the fail-closed blocked state.
3. Confirm the output contains
   `bootstrap_handoff_readiness_status=blocked`.
4. Confirm the reason is
   `bootstrap_handoff_readiness_reason=stage3_candidate:...`.
5. Confirm the output contains
   `bootstrap_handoff_remaining_gate_count=...` and
   `platform_acceptance_claimed=false`.

The blocked result is the expected default until the required platform-bound
evidence is supplied and independently reviewed. Do not rewrite it as a
platform PASS or use the checker self-test PASS as a substitute for platform
execution evidence.

## Evidence boundary

This lane covers command execution, exit status, readiness status, reason, and
the explicit no-platform-PASS claim. It excludes platform toolchain setup,
cross-host bootstrap execution, artifact provenance, deployment, and runtime
acceptance.
