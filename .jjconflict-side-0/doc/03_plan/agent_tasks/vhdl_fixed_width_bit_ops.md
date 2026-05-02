# VHDL-PARITY-004 Fixed-Width Bit Operations

## Ownership

Owner: Worker B

Status: Pending

Scope: docs and pending SPipe coverage for Python-HDL-compatible fixed-width
bit operation semantics. This task does not implement compiler lowering.

## Goal

Simple VHDL generation needs explicit, synthesis-stable semantics for sized
bit vectors before it can match Python-HDL generator behavior. Every operation
must preserve a predictable width, signedness, and VHDL representation so that
simulation and synthesis agree.

## Type Model

Fixed-width values should be modeled as sized unsigned and signed bit vectors:

- `bits[N]`: unsigned bit vector with width `N`.
- `sbits[N]`: signed bit vector with width `N`.
- `bool`: one-bit scalar control value, not implicitly interchangeable with a
  vector except through explicit conversion.

Widths must be compile-time constants after generic substitution. A zero or
negative width is a hard diagnostic. Unknown widths at VHDL emission are a hard
diagnostic unless the feature is explicitly represented as a VHDL generic.

## Width Semantics

Arithmetic follows Python-HDL-style explicit-width hardware behavior:

- Addition and subtraction produce width `max(lhs_width, rhs_width) + 1` unless
  the result is assigned through an explicit conversion or truncation.
- Multiplication produces width `lhs_width + rhs_width`.
- Unary negation on `sbits[N]` produces `sbits[N + 1]`.
- Bitwise `and`, `or`, and `xor` require equal widths or an explicit resize.
- Comparisons return `bool` and do not widen operands implicitly beyond a
  common explicitly resolved comparison width.

Implicit truncation is not allowed. Truncating assignment must be expressed as a
slice or explicit conversion so lost bits are visible in source.

## Shift Semantics

Shifts preserve the left operand width:

- Logical left shift: `bits[N] << k -> bits[N]`.
- Logical right shift: `bits[N] >> k -> bits[N]`.
- Arithmetic right shift: `sbits[N] >>> k -> sbits[N]`.

The shift amount must be unsigned and either compile-time bounded or emitted
with VHDL that cannot index outside the vector. Negative shift amounts are a
hard diagnostic. Overshifts fill with zeros for unsigned/logical shifts and the
sign bit for arithmetic right shifts.

## Slice Semantics

Slices are lower-inclusive and upper-exclusive in Simple source:

- A slice width is `end - start`.
- Out-of-range slices are hard diagnostics.
- Single-bit indexing of `bits[N]` returns `bool`.
- Multi-bit slicing returns `bits[width]` unless signed slicing is introduced
  as a separate explicit operation.

The VHDL backend may emit `downto` internally, but Simple source semantics must
remain independent from VHDL index direction.

## Concatenation Semantics

Concatenation is width additive and order preserving:

- `concat(a: bits[M], b: bits[N]) -> bits[M + N]`.
- `concat(bool, bits[N]) -> bits[N + 1]` after explicit bool-to-bit conversion
  or through a documented concat overload.
- Concatenating signed values returns unsigned `bits[...]` unless the result is
  explicitly converted to `sbits[...]`.

The left operand becomes the high-order bits in generated VHDL.

## Conversion Semantics

Conversions must be explicit whenever width or signedness changes:

- `resize_bits(x, N)` zero-extends or truncates only when truncation is named.
- `resize_sbits(x, N)` sign-extends or truncates only when truncation is named.
- `as_bits(x)` preserves width and reinterprets signedness.
- `as_sbits(x)` preserves width and reinterprets signedness.
- `to_bits(bool)` produces `bits[1]`.
- `to_bool(bits[1])` is allowed; wider vectors require an explicit comparison.

Unsupported implicit conversions should produce diagnostics before VHDL
generation.

## VHDL Lowering Expectations

Generated VHDL should use `ieee.numeric_std` for arithmetic:

- `bits[N]` lowers to `unsigned(N - 1 downto 0)`.
- `sbits[N]` lowers to `signed(N - 1 downto 0)`.
- `bool` lowers to `std_logic`.
- Explicit conversions lower through `resize`, `unsigned`, `signed`,
  `std_logic_vector`, or one-bit scalar adapters as needed.

Generated VHDL must pass GHDL analysis and a simulation fixture for arithmetic,
shift, slice, concat, comparison, and conversion examples.

## Pending Coverage

Pending coverage is tracked in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` under these cases:

- fixed-width arithmetic widens according to hardware width rules
- fixed-width bitwise operations reject ambiguous width mismatches
- fixed-width shifts preserve width and define overshift fill behavior
- fixed-width slices and single-bit indexes have deterministic result types
- fixed-width concatenation preserves operand order and sums widths
- fixed-width comparisons return bool with explicit operand sizing
- fixed-width conversions make resize, truncation, and signedness explicit

## Acceptance Criteria

This task is complete when implementation tasks replace the pending coverage
with runnable specs and all of these commands pass:

```sh
bin/simple test test/system/compiler/vhdl_fixed_width_bits_spec.spl
ghdl -a --std=08 <generated>.vhdl
ghdl -r --std=08 <testbench>
```
