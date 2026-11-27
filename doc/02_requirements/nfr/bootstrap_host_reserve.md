# Bootstrap host reserve constraints

- Keep the helper pure and constant-time, with scalar comparisons/subtractions
  only; no additional probes, allocations, environment reads or process calls.
- Preserve the existing positive-input arithmetic bounds: subtract only after
  proving the measured base exceeds the reserve, and select minima without
  multiplication.
- Keep failed bootstrap evidence and immutable producer identity. Use isolated
  output/cache ownership for native verification.
- Report runtime coverage accurately: eight native checks passed; the 19-case
  SSpec suite and full compiler qualification remain pending a usable self-hosted
  test CLI. Do not substitute a seed test run.

Verification: source review, working/staged facade audit and native before/after
fixture execution. No performance benchmark is needed for this scalar change.
