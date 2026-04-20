# Custom Primitive SFFI and Public API System Test Plan

Date: 2026-04-20

## Test Areas

1. Custom primitive declaration and layout.
2. SFFI exported classes using custom primitive fields.
3. SFFI functions using custom primitive parameters and returns.
4. SFFI bitfields using custom primitive backing and field types.
5. Public primitive API audit classification.
6. SimpleOS/HAL/SFFI migrated wrappers preserving behavior.

## Required Scenarios

- `newtype Fd = i32` is accepted in an exported SFFI class and maps to C `int32_t`/Simple `i32` ABI.
- `newtype Bytes = u64` is accepted as a function parameter and return in generated SFFI bindings without becoming an object pointer.
- `newtype GpioBits = u32` is accepted as a bitfield backing type.
- `newtype GpioMode = u8` works as a bitfield field with explicit `@bits(4)`.
- `newtype Ratio = f64` is rejected as a bitfield field with a diagnostic naming the non-integer underlying type.
- Public APIs in `src/os` that use handles/IDs are reported as convertible.
- Raw C extern declarations are reported as intentionally primitive or ABI-blocked, not as blind migration candidates.

## Verification Evidence

- Unit tests for resolver and lint behavior.
- Integration tests for SFFI generated signatures.
- Codegen tests for bitfield packing.
- Audit output checked for reason codes.
- Smoke checks required by repo policy for compiler/core/lib changes.
