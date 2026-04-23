# VHDL Python-HDL Parity Requirements

**Feature:** VHDL Python-HDL parity gaps `VHDL-PARITY-003` through `VHDL-PARITY-015`
**Selected scope:** Parity gaps
**Status:** Selected milestone complete with documented deferrals

## Requirements

- **REQ-VHDL-PARITY-003:** Named domains, reset polarity/synchrony/no-reset metadata, duplicate sanitized domain diagnostics, unsupported crossing diagnostics, and reset-aware backend lowering must be supported for the selected VHDL subset.
- **REQ-VHDL-PARITY-004:** Explicit fixed-width behavior must cover width propagation, resize/truncate/sign/zero extension, slice/concat, literal shifts, comparisons, and hard diagnostics for unsupported implicit-width cases.
- **REQ-VHDL-PARITY-005:** Source-facade interface tuples flatten deterministically from labeled fields, including one nested input bundle, and reject sanitized input/input and input/output VHDL port name collisions.
- **REQ-VHDL-PARITY-006:** Named and nested interface bundles must lower through deterministic flattened VHDL names, named wiring, source-map anchors, and collision diagnostics.
- **REQ-VHDL-PARITY-008:** Payload-free enums must lower in declaration order with sanitized VHDL literals, enum ports, literal assignments, and collision diagnostics.
- **REQ-VHDL-PARITY-009:** Payload enum lowering remains out of scope and must fail before VHDL emission with enum/variant-specific diagnostics.
- **REQ-VHDL-PARITY-010:** Helper subprogram support must classify supported helpers, emit deterministic VHDL function/procedure declarations and bodies, wire direct calls, and reject post-sanitization name collisions.
- **REQ-VHDL-PARITY-011:** ROM/RAM templates must support static ROM, registered ROM read, and explicit single-port synchronous RAM read-during-write policies; ambiguous, unconstrained, or unsupported memory patterns must fail before invalid VHDL emission.
- **REQ-VHDL-PARITY-012:** Testbench conversion for the milestone must cover one-DUT artifacts and ordered multi-DUT/multi-phase suites with literal stimuli, optional clock/reset setup, named port maps, equality assertions, source-map anchors, and simulator pass/fail behavior via `severity failure`.
- **REQ-VHDL-PARITY-013:** VHDL generation emits deterministic `.map.json` sidecars with generated entity, port, testbench, port-map, expectation, and diagnostic source-location anchors where source spans are available.
- **REQ-VHDL-PARITY-014:** Vendor synthesis smoke is opt-in by `SIMPLE_VHDL_VENDOR_SMOKE=1`, never blocks normal verification, and reports deterministic command, report, and log paths for disabled, missing-tool, and executed lanes.
- **REQ-VHDL-PARITY-015:** The support matrix and parity roadmap distinguish pure Simple source-of-truth support from compatibility source-facade coverage.

## Explicit Deferrals

Tagged-record payload enum lowering, floats, pointers, unit lowering, unconstrained memories outside the explicit ROM/RAM templates, broad HLS helper inference, implicit-width Python-HDL behavior outside the supported source-facade subset, unsupported MIR instructions, and the full pure-Simple compiler source-of-truth path are not enabled by default in this pass. They must remain hard diagnostics or explicit deferral diagnostics rather than partial VHDL output. Anonymous hardware outputs are not a stable VHDL public API; labeled outputs remain required for deterministic public ports.
