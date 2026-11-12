# Lambda body calling a private fn is visibility-checked at the callee module

- Date: 2026-11-12 · Status: open · Found by: p1-devhub lane
- Repro: `test/support/devhub1_provision.spl` passes `fn(k) -> [u8]: devhub1_csprng_bytes(k)`
  into `std.nogc_sync_mut.database.codec.sqlcipher4_page`. With `devhub1_csprng_bytes`
  private, the seed (phase-1, 2026-11-12) fails:
  `error: semantic: private fn devhub1_csprng_bytes of module ...devhub1_provision.spl is not visible to ...sqlcipher4_page.spl`
  and the spec executes 0 examples.
- Expected: a lambda's free identifiers resolve and are visibility-checked in its DEFINING module.
- Workaround (tagged `WORKAROUND(bug: lambda_private_fn_visibility_at_callee_2026-11-12)`): helper made `pub`.
