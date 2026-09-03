# Package Interface Requires Ranges

- Executable: `test/01_unit/app/pkg/requires_range_spec.spl`
- Requirements: `KPM-REQ-009`, `KPM-REQ-011`, `KPM-REQ-012`, `KPM-REQ-014`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- emits deterministic SDN accepted by the canonical parser.
- binds selected simple.sdn and ABI v1 when overrides are absent.
- rejects legacy and unknown policy state.
- selects the highest caret-compatible provider without backtracking.
- uses existing tilde satisfaction semantics.
- keeps caret and tilde branches live after manifest classification.
- uses lexical provider identity to break equal-version ties independent of input order.
- fails closed when no provider satisfies the range.
- is mutation-red if caret acceptance crosses a major boundary.
- rejects malformed provides and requires.
- does not classify comments strings or unrelated nested keys as interface ranges.
- classifies parsed dependency interface keys.
- fails closed for malformed parsed interface declarations.
- fails closed for malformed dependency sequence entries.
- classifies dependency sequences even before interface keys are added.
- rejects the legacy plugin.sdn manifest path.

## Selected Policy
- Manifest ownership: `simple.sdn`; ABI epoch: v1.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
