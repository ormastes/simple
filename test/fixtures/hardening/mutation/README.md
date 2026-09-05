# Hardening mutation fixtures

Minimal baseline trees consumed by `scripts/check/check-hardening-mutation.shs`.
Each `<gate_id>/baseline/` is copied into a private scratch dir, mutated, and fed
to the corresponding hardening gate via its `--root` argument. The harness
requires the gate to PASS on the unmutated baseline and FAIL on every mutation.

If a gate that lands later uses a different on-disk format, update the matching
baseline here (never the gate) so the mutation remains meaningful.
