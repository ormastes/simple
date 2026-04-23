# VHDL-PARITY-008/009: Enum Encoding and Payload Enums

Owner: Worker 4
Status: Pending
Scope: facade diagnostics, docs, and pending specs

## Goal

Define the VHDL contract for Simple enums in hardware code so payload-free
enums have stable encodings and payload enums have an explicit representation
strategy or a clear rejection diagnostic until full lowering is implemented.

## VHDL-PARITY-008: Payload-Free Enum Encoding

Payload-free Simple enums used in `@hardware` code should lower to deterministic
VHDL encodings.

Required behavior:

- Default encoding is declaration order, starting at zero.
- The generated VHDL type name and literals are sanitized with the same collision
  rules used for ports.
- Duplicate or colliding VHDL identifiers are hard errors.
- Enum values may be used as inputs, outputs, local values, equality operands,
  and `match` or branch discriminants when the backend supports the construct.
- The selected encoding must be stable across unrelated compiler changes.

Initial implementation option:

- Emit a VHDL enumerated type for payload-free enums when all consumers are VHDL
  code.
- For interoperability with bit-vector ports, add a later explicit encoding
  attribute or conversion path instead of changing the default representation.

Acceptance criteria:

- `enum State: Idle, Busy, Done` emits a stable VHDL enum declaration.
- Hardware ports of type `State` analyze with GHDL.
- Equality and branch selection over `State` simulate correctly.
- Sanitized literal collisions produce a diagnostic naming both Simple variants.

Verification:

```sh
bin/simple test test/system/compiler/vhdl_enum_encoding_spec.spl
ghdl -a --std=08 <generated>.vhdl
ghdl -r --std=08 <testbench>
```

## VHDL-PARITY-009: Payload Enums

Payload enums need an explicit hardware representation. Until that is
implemented, hardware lowering must reject them with a specific diagnostic
instead of emitting partial or invalid VHDL.

Preferred representation when implemented:

- Lower payload enums to a tagged record representation.
- The tag uses the same stable declaration-order encoding as payload-free enums.
- Each payload variant contributes deterministic record fields for its payload.
- Inactive payload fields are either reset to deterministic defaults or guarded
  by generated access logic; the chosen policy must be documented before
  implementation.
- Pattern matching lowers to tag comparisons plus payload field extraction.

Required interim rejection:

- Any payload enum crossing a hardware port boundary is a hard error.
- Any payload enum local value, return value, or match inside `@hardware` is a
  hard error until tagged-record lowering exists.
- The diagnostic must include `payload enum` and identify the enum or variant.

Facade slice status:

- The current Simple-side VHDL source facade cannot support enum-like constants
  without parser/backend changes because it only reads a single function
  declaration and has no top-level enum table or variant metadata.
- Runnable facade coverage now locks in rejection for enum declarations in the
  source text and for enum-like custom port types such as `State`.
- Precise `payload enum` diagnostics remain part of the real enum lowering
  task, where the compiler has access to enum declarations and payload shape.

Acceptance criteria:

- Payload enum ports are rejected before VHDL emission with a precise diagnostic.
- Payload enum locals and returns are rejected before VHDL emission.
- Once tagged-record lowering is implemented, GHDL analysis and simulation cover
  tag selection, payload extraction, and inactive-field behavior.

Verification:

```sh
bin/simple test test/system/compiler/vhdl_payload_enum_spec.spl
ghdl -a --std=08 <generated>.vhdl
```

## Dependencies

- VHDL identifier sanitization and collision diagnostics.
- Fixed-width bit semantics if explicit binary encodings are added.
- Testbench conversion for full simulation coverage of branch and payload
  behavior.

## Non-Goals

- Do not implement enum lowering in this task.
- Do not choose vendor-specific enum encoding attributes yet.
- Do not support payload enum synthesis by silently flattening arbitrary data
  without a documented tagged representation.
