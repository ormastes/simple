# Native Render Log Matrix PIX Fixture Reason Mismatch

## Closed 2026-09-13 — recorded as fixed in-lane; no contradicting evidence in the tree
- **measured**: `test/03_system/check/native_render_log_platform_matrix_contract_spec.spl` exists, so the fix was not achieved by deleting coverage.
- **inferred**: the entry's own status already reads "fixed in the same 2026-06-28 lane".
- **inferred**: the spec could not be re-run — `bin/simple test` is broken on this Windows host (a trivial 1-assertion spec also reports `reason=outer-bound-timeout budget_ms=930000` in under a second).
- **inferred**: the residual it describes lived in a per-run build artifact (`build/test-native-render-log-.../evidence.env`) that does not exist in this checkout.

Date: 2026-06-28

## Summary

`test/03_system/check/native_render_log_platform_matrix_contract_spec.spl`
now passes with the fixed SSpec runner. The previously remaining failure was in
`rejects Windows D3D12 rows whose PIX file-byte proof is missing`.

**Status:** CLOSED 2026-09-13 (see Closed section above)

## Observed Evidence

`build/test-native-render-log-platform-matrix-pix-file-magic/out/evidence.env`
reports:

- `windows_d3d12_render_log_compare_status=fail`
- `windows_d3d12_render_log_compare_reason=windows-d3d12-pix-artifact-file-not-pass:<missing>`
- `windows_d3d12_render_log_compare_pix_artifact_file_status=`
- `windows_d3d12_render_log_compare_pix_artifact_file_magic=`

The scenario currently expects:

- `windows_d3d12_render_log_compare_reason=windows-d3d12-pix-artifact-file-magic-not-pix:<missing>`

## Fix Applied

The scenario is meant to exercise file-byte magic validation, so it now adds
`windows_d3d12_render_log_compare_pix_artifact_file_status=pass` to that
fixture while leaving `windows_d3d12_render_log_compare_pix_artifact_file_magic`
missing.

Focused verification:

```sh
bin/simple test test/03_system/check/native_render_log_platform_matrix_contract_spec.spl --mode=interpreter --clean --fail-fast
```

Result: `7 examples, 0 failures`.
