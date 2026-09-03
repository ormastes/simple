# AspectParamsV1 Environment Boundary

- Executable: `test/01_unit/compiler/aop/aspect_params_spec.spl`
- Requirements: `KPM-REQ-002`, `KPM-REQ-005`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- decodes values and marks only explicitly supplied ordinals present.
- keeps every presence bit clear for absent values.
- selects atomic APK-only and rejects the legacy dual extension.
- keeps direct CompileOptions constructors source-compatible.

## Selected Policy
- Coverage defaults to atomic APK-only typed extension data; explicit dual data
  is retained only as rejection evidence.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
