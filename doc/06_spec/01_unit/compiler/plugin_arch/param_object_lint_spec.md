# Versioned Parameter-object Lint

- Executable: `test/01_unit/compiler/plugin_arch/param_object_lint_spec.spl`
- Requirements: `KPM-REQ-005`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- accepts an append-only parameter object with hdr first and ext last.
- reports PARAM-001 when the header or extension boundary is invalid.
- reports PARAM-002 when V2 changes a V1 ordinal.
- reports PARAM-003 for compiler-side AOP environment reads.
- does not treat comments or string data as environment reads.
- reports PLUG-001 when a port has no trailing extension field.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
