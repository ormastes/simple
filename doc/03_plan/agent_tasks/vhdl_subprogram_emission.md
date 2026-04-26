# VHDL Subprogram Emission Task

Date: 2026-04-23
Task ID: VHDL-PARITY-010
Owner: Worker D
Status: Pending

## Goal

Make the VHDL backend emit reusable VHDL subprograms for Simple helper
functions when doing so preserves hardware semantics and improves generated
VHDL readability. Keep entity lowering for hardware boundaries, stateful logic,
and any helper that needs ports, instances, or process semantics.

## Lower to VHDL Functions

Lower a Simple helper to a VHDL `function` when all of these are true:

- The helper is pure combinational logic.
- Inputs and return values are scalar or supported fixed-width values.
- The helper has a single return value or a labeled tuple return that can be
  represented as a backend-defined record type.
- The helper has no clock, reset, storage, heap allocation, pointer, dynamic
  indexing, indirect call, unsupported intrinsic, or I/O behavior.
- The helper is called from hardware code but is not itself required to be a
  public entity boundary.

The emitted VHDL function must be placed in a deterministic declarative region
before the architecture body that calls it.

## Lower to VHDL Procedures

Lower a Simple helper to a VHDL `procedure` when all function rules hold except
that the helper naturally has multiple output values and record-return lowering
would obscure direct signal assignment. Procedure outputs must use named `out`
parameters derived from labeled return fields.

Anonymous distinct-type multi-returns may lower to deterministic procedure
outputs `out0`, `out1`, and so on only while the common anonymous-output warning
remains in force. Repeated same-type anonymous returns stay rejected before VHDL
emission.

## Keep Entity Lowering

Do not lower a helper to a subprogram when any of these are true:

- The function is decorated with `@hardware` and is part of the public generated
  hardware hierarchy.
- The function uses `@clocked`, reset/domain metadata, memory inference, or any
  stateful process semantics.
- The function requires component instantiation or calls another entity that
  cannot be represented as a subprogram call.
- The function has interface bundle ports, bidirectional ports, composite ports
  not representable by supported records, or generics that must remain entity
  generics.
- The generated VHDL needs observable hierarchy for synthesis constraints,
  source maps, vendor debug flows, or testbench wiring.

Entity lowering remains the conservative fallback whenever subprogram eligibility
is ambiguous.

## Naming and Mangling

- Sanitize every Simple identifier with the same VHDL identifier sanitizer used
  for entity and port names.
- Prefix generated helper subprogram names with `simple_fn_` unless the backend
  already owns a stronger collision-free namespace.
- Include enough module and monomorphization information to avoid collisions
  between overloaded, generic, or same-named helpers.
- Preserve source label names for procedure output parameters when possible.
- Reject duplicate names after VHDL sanitization within a subprogram signature.
- Reject collisions between generated subprogram names, entity names, signal
  names, record type names, and reserved VHDL words.

## Diagnostics

The first implementation must add precise diagnostics for:

- A helper requested or selected for subprogram lowering but containing stateful
  or unsupported behavior.
- A label, parameter, return field, or generated helper name colliding after
  VHDL sanitization.
- A multi-return helper that cannot be represented as either a record-returning
  function or procedure.
- A call graph cycle among helpers selected for subprogram emission.

## Pending SPipe Coverage

Pending coverage lives in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` until the
implementation adds runnable system specs, expected generated VHDL fixtures, and
GHDL checks.

Required future runnable coverage:

- Pure single-return helper emits one VHDL function and callers invoke it.
- Pure labeled multi-return helper emits either a record-returning function or a
  procedure with named output parameters.
- `@hardware` public boundaries remain entities even when their body is pure.
- `@clocked` or reset/domain helpers remain entities or processes, not VHDL
  functions.
- Subprogram names are deterministic and collision-safe after sanitization.
- Unsupported helper behavior fails with a specific diagnostic before VHDL text
  is emitted.

## Verification

Focused implementation gate:

```sh
bin/simple test test/system/compiler/vhdl_subprogram_spec.spl
ghdl -a --std=08 <generated>.vhdl
```

Full parity gate contribution:

```sh
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
cargo check -p simple-compiler -p simple-driver
```
