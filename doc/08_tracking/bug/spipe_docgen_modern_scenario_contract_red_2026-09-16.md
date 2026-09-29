# spipe-docgen does not recognize modern `it("...")` call-form scenarios; scenario-body rendering contract red

Date: 2026-09-16
Specs:
- test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl (2 of 6 fail)
- test/01_unit/app/tooling/spipe_docgen_modern_spec_family_scan_spec.spl (1 of 2 fails)
- test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl (21 of 65 fail)

## Observed
- `is_scenario_line` (`src/app/spipe_docgen/spipe_docgen/parser.spl:1076`) only accepts `it "/"slow_it "/"pending "/"skip_it "/"skip it ` prefixes (legacy bare form). The modern call form `it("does the thing"):` is rejected, so `validate_spec(...).docs_present` is false for every spec file written in call form. The family-scan spec lists 5 real offenders under `src/lib/hardware/nand_emu/test/` that are all reported scenario-less.
- scenario_body_spec: 21 rendering failures including: dedented code-fence rendering, escaped quotes in step labels, same-line oracle markers kept out of expected values, CSS identifiers ending in `m` kept out of math blocks, pending-return classification, capture metadata rendering (bare/explicit/off), folded executable source, manual step derivation from control flow, empty-metadata warnings, golden math_blocks capture, tier mirroring, fail-closed inputs, scenario placement after title.

## Impact
The docgen pipeline under-reports or mis-renders every modern-syntax spec; generated manuals for call-form suites are wrong or absent.

## Expectation
`is_scenario_line` (and the counting/rendering paths built on it) must accept the modern call form; the scenario_body failures are a rendering-contract gap between the generator and the spec's documented golden outputs.

## Unblock condition
A docgen lane extending parser.spl scenario recognition and the renderer to the spec's contract; per testing rules the assertions were not softened.
