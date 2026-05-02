# VHDL-PARITY-006 Interface Bundles

Owner: Worker C
Status: Pending

## Goal

Add a stable public interface-bundle model for `@hardware` VHDL generation so
related ports can be declared and wired as a named group while still lowering
to portable VHDL ports.

## Proposed Syntax

Bundle types are ordinary labeled tuple types with a hardware-facing alias:

```simple
type AxiLiteRead = (
    addr: bits[32],
    valid: bool,
    ready: bool
)

@hardware
fn slave(read: AxiLiteRead) -> (data: bits[32], done: bool):
    ...
```

Nested bundles remain labeled tuple fields:

```simple
type BusPair = (
    cmd: AxiLiteRead,
    rsp: (data: bits[32], valid: bool)
)
```

Implementation may later add explicit bundle decorators, but the first parity
target should use labeled tuple aliases so the syntax composes with existing
labeled tuple support.

## Flattening And Naming

VHDL port names are formed from the parameter name plus the full field path:

- `read.addr` becomes `read_addr`
- `read.valid` becomes `read_valid`
- `pair.cmd.addr` becomes `pair_cmd_addr`
- `pair.rsp.data` becomes `pair_rsp_data`

Each segment is sanitized with the same VHDL identifier sanitizer used for
functions, parameters, and return fields. The flattened path is then joined
with `_`.

Flattening is deterministic and source-order preserving. The order is depth
first, left to right, matching the labeled tuple field order in the type.

## Collision Diagnostics

The compiler must reject any bundle whose flattened VHDL port names collide
after sanitization.

Examples that must fail:

```simple
type Bad = (data_ready: bool, data.ready: bool)
```

```simple
type Bad = (class: bool, class_: bool)
```

The diagnostic should name:

- the hardware function
- the bundle parameter or return field being flattened
- both original field paths
- the final colliding VHDL identifier

## Caller/Callee Wiring

Hardware calls remain ordinary Simple calls. In VHDL lowering, bundle wiring is
named by the same flattened paths on both sides.

```simple
@hardware
fn pipe(input: AxiLiteRead) -> (output: AxiLiteRead):
    return (output: input)

@hardware
fn top(bus: AxiLiteRead) -> (done: bool):
    val p = pipe(bus)
    return (done: p.output.valid)
```

Expected lowering:

- callee entity exposes `input_addr`, `input_valid`, `input_ready`, and
  corresponding output ports
- caller allocates one signal per flattened returned field
- `port map` connects by flattened name, not by position
- field access like `p.output.valid` resolves to the returned temp signal for
  `output_valid`

## Acceptance Criteria

- Named interface bundles lower to grouped flattened VHDL ports.
- Nested bundles flatten recursively with deterministic names.
- Collisions after sanitization are hard errors.
- Hardware call lowering wires caller and callee bundles by flattened names.
- Generated VHDL for bundle fixtures passes `ghdl -a --std=08`.

## Verification

```sh
bin/simple test test/system/compiler/vhdl_interface_bundles_spec.spl
ghdl -a --std=08 <generated>.vhdl
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
```
