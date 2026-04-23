# VHDL-PARITY-013/014: Source Maps and Vendor Synthesis Smoke

Owner: Worker E
Status: Pending
Scope: Docs/tests only until implementation starts.

## Goal

Bring Simple VHDL generation closer to Python-HDL workflows by making generated
VHDL traceable back to Simple source and by adding optional vendor synthesis
smoke checks that confirm accepted hardware subsets remain synthesis-friendly.

These tasks must not make vendor tools mandatory for normal development. GHDL
analysis, elaboration, simulation, and `ghdl --synth` stay the portable baseline.

## VHDL-PARITY-013: Source Map Sidecar

Emit a deterministic source-map sidecar next to generated VHDL. The initial
format should be JSON so tests and external tools can inspect it without a
custom parser.

Required sidecar content:

- Generator version and source file path.
- Generated VHDL file path and top entity name.
- Mapping entries from generated VHDL line/column spans to Simple source
  line/column spans.
- Stable generated object identifiers for entities, ports, signals, processes,
  component instances, subprograms, memories, enum encodings, and testbench
  artifacts.
- The Simple symbol path for each mapped object when available.
- Sanitized VHDL names plus original Simple names for collision diagnostics.

The map must be stable across repeated builds when input source and compiler
options are unchanged.

## Diagnostic Expectations

Diagnostics produced while lowering or validating VHDL must include source-map
anchors when a Simple origin exists. At minimum:

- Unsupported hardware construct diagnostics point to the source expression or
  declaration that triggered lowering failure.
- VHDL identifier sanitization collisions report all colliding Simple names and
  the generated VHDL name.
- Vendor smoke failures report the generated VHDL object, source-map origin, and
  tool command that failed.
- Diagnostics for generated-only artifacts still identify the nearest owning
  Simple hardware function, process, or testbench.

## VHDL-PARITY-014: Vendor Synthesis Smoke

Add optional vendor synthesis smoke tests for supported generated fixtures.
These tests should run only when the matching tool is available and explicitly
enabled by environment or test flag.

Expected behavior:

- Missing vendor tools produce a skipped test with the tool name and expected
  environment variable, not a failure.
- Portable smoke always runs through GHDL before vendor-specific checks.
- Vendor commands write logs and generated reports under `build/` or another
  ignored artifact directory.
- Each vendor smoke test records the generated VHDL fixture, top entity,
  command line, exit status, and source-map sidecar path.
- Failures summarize the first actionable synthesis diagnostic and include
  source-map context when available.

Candidate environment gates:

- `SIMPLE_VHDL_VENDOR_SMOKE=1` enables optional vendor smoke specs.
- `SIMPLE_VHDL_VENDOR=vivado|quartus|yosys|ghdl-synth` selects a tool profile.
- `SIMPLE_VHDL_VENDOR_BIN` overrides the tool executable path.

## Acceptance Criteria

- Generated VHDL has a JSON source-map sidecar with stable object mappings.
- Unsupported construct and name-collision diagnostics include source-map
  origin information.
- GHDL baseline smoke still runs without vendor tools.
- Vendor synthesis smoke skips cleanly when tools are unavailable or disabled.
- Vendor synthesis smoke runs for at least one available profile and reports
  source-map-linked failures.

## Pending SSpec Coverage

Pending coverage lives in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` until implementation
adds runnable specs and tool-specific fixtures. Runnable specs should later move
to:

- `test/system/compiler/vhdl_source_map_spec.spl`
- `test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl`

## Verification Commands

```sh
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
bin/simple test test/system/compiler/vhdl_source_map_spec.spl
bin/simple test test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl
ghdl -a --std=08 <generated>.vhdl
ghdl -e --std=08 <entity_or_testbench>
ghdl --synth --std=08 <entity>
SIMPLE_VHDL_VENDOR_SMOKE=1 SIMPLE_VHDL_VENDOR=<vendor> bin/simple test test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl
```
