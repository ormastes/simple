# Bootstrap platform handoff readiness test plan

## Scope

This plan covers the checker self-test and the checker default invocation.
The lane verifies that the default handoff is blocked until platform evidence
exists and that a checker self-test PASS cannot be promoted to a platform
PASS. It excludes platform bootstrap execution, artifact production,
deployment, and target-host acceptance.

## Shared flow

Both executable scenarios call the exact shared helper
`step_bootstrap_platform_handoff_readiness`. The operator-visible flow is
mirrored in
`doc/06_spec/03_system/check/bootstrap_platform_handoff_readiness_spec.md`.

## Readiness traceability

| Readiness ID | Scenario | Executable assertion | Manual flow |
|---|---|---|---|
| BPHR-001 | Checker self-test claim boundary | Runs `--self-test` and requires exit code `0` plus `bootstrap_handoff_self_test=pass` | Scenario BPHR-001/BPHR-002, steps 1-3 |
| BPHR-002 | Checker self-test claim boundary | Requires `platform_acceptance_claimed=false` in self-test output | Scenario BPHR-001/BPHR-002, step 4 |
| BPHR-003 | Default blocked handoff | Runs the checker with no mode flag and requires fail-closed exit code `1` plus `bootstrap_handoff_readiness_status=blocked` | Scenario BPHR-003/BPHR-004, steps 1-3 |
| BPHR-004 | Default blocked handoff | Requires a `stage3_candidate:` reason, remaining-gate count, and `platform_acceptance_claimed=false` | Scenario BPHR-003/BPHR-004, steps 4-5 |

## Execution order

1. Run BPHR-001 and BPHR-002 with the checker `--self-test` mode.
2. Run BPHR-003 and BPHR-004 with the checker default invocation.
3. Preserve the emitted text as checker evidence; do not infer platform
   acceptance from either command.

## Pass and fail criteria

Pass requires self-test exit `0`, default blocked exit `1`, the self-test marker
to be present, the default status to be `blocked`, the default reason to begin
with `stage3_candidate:`, and both modes to emit
`platform_acceptance_claimed=false`.

Fail if either command is missing, the self-test exits nonzero, the default
blocked check exits with anything other than `1`, a required marker is omitted,
a platform PASS is claimed, or the default reason changes without updating this
plan and the mirrored manual.

## Manual rendering policy

Both scenarios are primary operator-visible scenarios. The shared helper is
setup-only and is represented in the executable source; the manual exposes
the concrete shell commands and expected output instead of hiding the flow.
No capture artifact is required because the checker emits text evidence.

## Risks and exclusions

The checker self-test may pass while every target platform remains unverified.
The blocked default is therefore intentional and release-blocking for the
platform handoff. This SPipe lane does not validate host prerequisites,
cross-platform artifacts, provenance hashes, or live bootstrap behavior.
