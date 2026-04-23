# VHDL-PARITY-011: ROM/RAM Inference

Owner: Worker D
Status: Pending
Scope: Docs/tests only until implementation starts.

## Goal

Bring Simple VHDL memory generation to Python-HDL parity for memory patterns
that synthesis tools reliably infer as ROM or RAM. Generated VHDL should use
idiomatic array declarations and clocked processes instead of expanding
memories into large combinational muxes except for explicitly tiny or irregular
patterns.

## Static ROM Patterns

Supported static ROM sources:

- Compile-time constant arrays indexed by a fixed-width unsigned address.
- Constant lookup tables with scalar, bit-vector, enum, or flattened record
  elements once those element types are supported by the VHDL backend.
- Optional registered-output ROMs when the source marks the read as clocked.

ROM read policies:

- Combinational ROM emits a constant array declaration plus indexed read.
- Registered ROM emits a synchronous process with documented one-cycle latency.
- Dynamic indexes must have statically known width or an explicit range.
- Out-of-range behavior must be explicit: reject provably invalid indexes, or
  require a documented default/checking mode for dynamic indexes.

## Supported RAM Patterns

Supported RAM sources:

- Single-port synchronous RAM with one read/write port.
- Simple dual-port RAM with one read port and one write port.
- True dual-port RAM only after conflict semantics are specified.
- Optional initialization from a static table when the selected synthesis flow
  supports it; otherwise emit a clear warning or sidecar initialization path.

RAM write policies:

- Writes occur on a named clock edge.
- Write enable is a scalar boolean/std_logic-compatible condition.
- Address and data widths are statically known.
- Partial writes require byte-enable or lane-enable representation and are a
  separate acceptance item.

RAM read-during-write policies:

- The source must choose or inherit a documented policy: `read_first`,
  `write_first`, or `no_change`.
- Unsupported ambiguous same-address read/write behavior is rejected with a
  specific diagnostic instead of relying on vendor defaults.
- Generated VHDL preserves the chosen policy in a form GHDL and at least one
  vendor synthesis tool can infer.

## VHDL Shape

Expected generated VHDL shape:

- A named array type for each inferred memory.
- A signal or constant of that array type.
- Indexed reads and clocked writes using sanitized, collision-safe names.
- Optional synthesis attributes only behind a target option; portable VHDL is
  the default.

The backend must keep source-level memory names stable enough for source maps
and diagnostics to identify the originating Simple declaration.

## Acceptance Criteria

- Static combinational ROM fixture analyzes with GHDL and synthesizes without
  golden-output evidence of hand-expanded case/mux logic.
- Registered ROM fixture analyzes, elaborates, and simulates expected latency.
- Single-port RAM fixture simulates write/read behavior for the selected
  read-during-write policy.
- Simple dual-port RAM fixture simulates independent read and write ports.
- Unsupported ambiguous RAM patterns produce specific diagnostics.
- Optional vendor synthesis smoke confirms memory inference or skips with a
  clear unavailable-tool reason.

## Pending SSpec Coverage

Pending coverage lives in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` until implementation
creates runnable system specs. Runnable specs should later move to:

- `test/system/compiler/vhdl_memory_inference_spec.spl`
- `test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl` for optional
  vendor inference confirmation.

## Verification Commands

```sh
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
bin/simple test test/system/compiler/vhdl_memory_inference_spec.spl
ghdl -a --std=08 <generated>.vhdl
ghdl -e --std=08 <entity_or_testbench>
ghdl -r --std=08 <testbench>
ghdl --synth --std=08 <entity>
```
