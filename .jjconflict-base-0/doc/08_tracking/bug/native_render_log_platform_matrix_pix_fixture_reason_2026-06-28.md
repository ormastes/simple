# Native Render Log Matrix PIX Fixture Reason Mismatch

Date: 2026-06-28

## Summary

`test/03_system/check/native_render_log_platform_matrix_contract_spec.spl`
now passes with the fixed SSpec runner. The previously remaining failure was in
`rejects Windows D3D12 rows whose PIX file-byte proof is missing`.

Status: fixed in the same 2026-06-28 lane.

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
