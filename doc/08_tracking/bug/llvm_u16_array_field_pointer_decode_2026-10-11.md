# u16 array field decoded as a pointer

Status: integrated-candidate ARM fixture and RISC-V object PASS; isolated release-head and broader gates pending.
Requirement: REQ-MIR-ARRAY-FIELD-SHAPE.

The exhaustive LLVM matrix failed `parse_lex_program_valid` in
`src/lib/common/structural/parse/parse_types.spl` with `unsupported LLVM value
conversion from i16 to ptr`. GDB places the rejection in `translate_binop` via
`value_as_type`, not a source cast or MIR Bitcast. The small fixture
`test/fixtures/compiler/u16_array_comparison.spl` reproduces the same rejection
in `field_zero`, comparing `flags.values[0]` with `0u16`.

`register_composite_field_metadata` assigned `__runtime_array__` to every
Array/Slice field. The index reader uses that marker to identify an element
which itself contains an array, and therefore decoded the numeric element as
`Slice(u16)`. LLVM correctly rejected coercing the comparison's u16 constant
to the erroneous pointer operand type. Draft PRs #2838 and #2840 concern legal
integer/pointer Bitcast lowering and do not repair this lost element contract.

The repair emits that marker only for Array/Slice *elements*. Named elements
keep their owner name; scalar elements have no aggregate marker. Full declared
field/element HIR types and runtime array field tracking remain in place.
The prior array-index HIR provenance repair is unchanged. LLVM conversion
checks are unchanged.

Authored metadata specs cover u16, text, and nested u16 arrays. The native
fixture covers plain and field u16 reads, zero/high unsigned values, bit masks,
and nested field reads. These native controls passed with the coordinated
rebuilt producer; authored metadata spec execution remains pending.

Baseline producer SHA256:
`67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`.
Local evidence: `build/native_probe/llvm-cast-roots/parse-before-gdb.log` and
`u16-before.log`. The inferior aborted; GDB's process exit zero is not a pass.

Final scoped native qualification and exact receipts: [verification](../verification/native_array_field_elements_2026-10-11.md). Authored unit execution and standalone PR-head admission remain pending.
