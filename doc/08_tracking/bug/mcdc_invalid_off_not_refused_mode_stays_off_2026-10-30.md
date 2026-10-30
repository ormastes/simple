# MC/DC invalid-off is flagged but never refused; SIMPLE_MCDC_MODE stays off

- Where: src/lib/nogc_sync_mut/test_runner/test_runner_config.spl:245-249 (propagate_env_vars)
- Repro: SIMPLE_MCDC_MODE=off, no waiver env, `simple test --profile=strict <spec>`.
  SIMPLE_MCDC_MODE_ERROR=invalid-off is set, SIMPLE_MCDC_MODE keeps "off", and no code
  reads SIMPLE_MCDC_MODE_ERROR (grep src/), so MC/DC is silently disabled with exit 0.
  Same for invalid-mode (bogus value left in env).
- Expected: non-zero exit with an explicit refusal; mode never left as off.
- Specs: test/01_unit/app/test_runner_new/mcdc_propagate_env_spec.spl (2 red examples:
  "does not leave SIMPLE_MCDC_MODE=off ...", "does not leave a bogus mode ..."),
  generalisation: mcdc_mode_resolution_spec.spl (green, resolver itself is correct).
- Unblock: runner main must check SIMPLE_MCDC_MODE_ERROR after propagate_env_vars and exit non-zero.
