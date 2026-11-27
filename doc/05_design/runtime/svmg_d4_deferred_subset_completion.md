# SVM-G D4 integer printing and float compound assignment

This repair completes both gaps recorded by `svmg_d4_lowering_deferred_subset_2026-08-07`, under the existing GPU remote interpreter design section 4.4. It changes the Pure-Simple HIR-to-SVM-G owner, not the VM instruction set.

## Integer printing

Use checked `HirTypeKind.Int(bits: 32, signed: ...)` to distinguish i32 from u32. An untyped integer literal may be accepted only when its suffix and range identify a supported 32-bit value. Unsupported widths, unknown types and noninteger values must produce a diagnostic rather than silently reinterpret their bits.

Evaluate the argument once. Each print site reserves distinct aligned scratch storage through the existing DATA allocator: three words for the current magnitude, half magnitude and digit count, followed by twelve bytes for up to ten decimal digits. Reserve before emitting argument evaluation so nested helper calls cannot alias the site's storage. Reset its count on every execution.

For a negative signed value, emit a minus sign and compute the magnitude with the VM's wrapping subtraction. The resulting magnitude is an unsigned word, including the i32 minimum's `0x80000000` representation. A u32 never emits a minus sign.

Decimal extraction uses existing logical `SHR` and signed positive division. Let `h = n >>> 1`, `q = h / 5`, and `digit = 2 * (h % 5) + (n & 1)`. Since `n = 2h + (n & 1)`, this gives `n = 10q + digit`, with `digit` in 0..9. The division operands fit signed i32 even when the original unsigned magnitude does not. Preserve the original low bit until the digit is stored, then replace the magnitude with q. A do-once loop emits zero correctly. Store ASCII digits with STORE8, then emit them in reverse with LOAD8 and SYS_PUTC.

The production reference VM already defines SHR as a logical u32 shift and provides byte loads/stores. No VM change or special constant output is required for signed minimum or unsigned maximum. No newline is added, preserving literal-print behavior.

## Float compound assignment

Extend the existing assignment-opcode selector with an optional float flag. Float Add/Sub/Mul/Div select FADD/FSUB/FMUL/FDIV; ordinary integer mappings remain unchanged. Retain the existing local load/RHS evaluation/store sequence. Float remainder, bitwise and shift operators remain unsupported with an explicit diagnostic. This repair does not choose a mixed numeric promotion policy.

## Evidence

Tests must build real HIR, invoke the changed lowerer and execute its bytecode in the existing reference VM. Decimal output covers i32 zero, sign, boundaries, u32 high-bit values, computed/local values, repeated print sites and an argument helper with an observable print side effect. Float tests observe runtime arithmetic results for all four operators, with integer controls and unsupported-operator negatives.

Source review and static checks are separate from execution qualification. The self-hosted test runner, required compiler/core/MCP checks and merged release PR remain mandatory before reporting this bug fixed. Current status: implementation and executable tests being prepared; verification UNRUN.
