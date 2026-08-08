# Unlimited Stage4 profile disables structural streaming ownership

- Date: 2026-08-03
- Status: fixed — `/root/option_native_codegen_rootcause`
- Bug ID: `stage4_unlimited_disables_streaming_ownership`
- Severity: P1

## Symptom

The `incremental-unlimited` and `clean-release` profiles keep all CPU workers
but also set `SIMPLE_BOOTSTRAP_LOW_MEMORY=0`.  The pure-Simple streaming
selector requires `ctx.options.low_memory`, so the explicit
`SIMPLE_STAGE4_STREAMING_SURFACES=1` gate becomes inert and Stage4 retains the
full rich parser graph.

## Fix contract

Structural streaming ownership is independent of CPU/thread resource limits.
Keep the explicit AOT, bootstrap, entry-closure, Stage4, streaming-request, and
non-VHDL gates.  Full-resource profiles continue using every selected worker
while also retaining the per-file ownership/reclamation path.

## Verification

- `stage4_unlimited_streaming_ownership_spec.spl`: 3 examples, 0 failures;
- bootstrap producer and portability-gate shell syntax: pass;
- the broader bootstrap portability gate passed the B1 ownership/profile
  assertions, then stopped on the unrelated pre-existing retired-Windows-
  workflow restoration assertion.

No Stage4 build was run for this focused configuration fix.
