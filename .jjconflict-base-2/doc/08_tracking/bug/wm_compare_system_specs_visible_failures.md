# wm_compare System Specs Visible Failures

After moving the former `test/sys/wm_compare` suite to
`test/system/wm_compare`, focused SPipe runs exposed existing system-spec
failures that should not be hidden by layout migration.

Passing moved specs:

- `test/system/wm_compare/html_compat_spec.spl`
- `test/system/wm_compare/emulated_capture_spec.spl`
- `test/system/wm_compare/famous_site_engine2d_backend_spec.spl`

Failing moved specs:

- `test/system/wm_compare/v1_v2_parity_spec.spl`: parity result booleans are
  false after replacing obsolete `to_be_true()` matcher calls with
  `to_equal(true)`.
- `test/system/wm_compare/golden_gate_spec.spl`: golden files load and PPM
  round-trip passes, but drift-budget checks are false.
- `test/system/wm_compare/v1_v3_parity_spec.spl` and
  `test/system/wm_compare/v1_v4_parity_spec.spl`: fail because
  `BrowserCompositorBackend` no longer exposes the `clear` method expected by
  the parity harness.

The migration fixed matcher syntax and stale module imports, but these
behavioral failures need owner review before the whole wm_compare suite can be
used as a release gate.
