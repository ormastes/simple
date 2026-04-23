# VHDL Python-HDL Parity Detail Design

## Backend

- Validate enum variants before package emission.
- Sanitize enum literal names with the existing VHDL identifier sanitizer.
- Reject enum literal collisions after sanitization before package emission.
- Reject payload variants with a diagnostic that names the enum and variant.
- Emit active-low and active-high reset conditions from MIR clock-domain metadata, preserve synchrony, and emit clock-only processes when no reset signal is present.
- Reject duplicate sanitized clock-domain names and unsupported crossings through the VHDL constraint checker before emission.
- Continue using MIR VHDL instructions for resize, slice, concat, port maps, and process lowering.
- Emit supported helper subprogram declarations/bodies through package output and reject sanitized helper-name collisions.
- Render static ROM, registered ROM read, and single-port synchronous RAM templates only when read-during-write policy is explicit.

## Driver Facade

- `aot_vhdl_file` writes generated VHDL and a deterministic source-map sidecar.
- Sidecar JSON includes version, source path, generated path, backend label, entity anchors, and port anchors.
- Existing source-facade parsing remains compatibility-only and is covered by system specs.
- Source-facade `@clocked` supports the implemented active-low/active-high async reset forms and active-low synchronous reset form.
- Source-facade tuple input flattening checks sanitized input/input and input/output port collisions before writing VHDL.
- Source-facade named and nested bundle aliases lower to deterministic flattened names with named wiring and source-map anchors.
- Source-facade fixed-width support is conservative: fixed integer ports, arithmetic/logic, literal shifts, one-level slices, explicit `concat`, unary operations, comparisons, extension/truncation through explicit casts, and width mismatch diagnostics.

## Testbench Renderer

- `compiler.backend.vhdl.vhdl_testbench.render_vhdl_testbench` renders a minimal testbench artifact for one DUT.
- The implemented renderer supports literal stimuli, named DUT port maps, optional clock/reset driving, and equality assertions with `severity failure`.
- The artifact includes deterministic source-map JSON anchors for the source test name, DUT ports, generated port-map lines, and expectation assertions.
- Multi-DUT and multi-phase source-test conversion remain deferred.

## Vendor Smoke

- `test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl` checks the opt-in/skip contract.
- Vendor execution is enabled only when `SIMPLE_VHDL_VENDOR_SMOKE=1`.
- Disabled or missing-tool lanes report clear diagnostics with deterministic report and log path fields.
