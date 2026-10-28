# Shared execution scheduling requirements

These requirements record the user's selected behavior directly; no alternative
feature options were selected or retained.

- REQ-001: Ordinary parallel tests and the build runner use one shared execution
  scheduling owner for readiness, reservation, reap and terminal transitions.
- REQ-002: Both retain the canonical shared async process backend. Domain
  adapters retain build receipt validation and test capture/assertion handling.
- REQ-003: Parent alone mutates scheduling state and commits results. Do not
  add a lockless map without demonstrated concurrent-writer need.
- REQ-004: Preserve admission limits, deadlines, cancellation and timeout
  distinctions, reap-before-release, retry policy and input-order reporting.
- REQ-005: Preserve real green/red/zero-example behavior and canonical
  --assert-ran evidence under the GNU-only phase2 producer. No seed fallback.
- REQ-006: Keep the existing live baseline build frozen; verify the changed
  implementation separately and land only a reviewed, verified PR.
