# Inherited code-point cast failure calls the wrong panic ABI

Status: source repair and authored regressions; native proof PENDING.
Requirement: REQ-MIR-CODEPOINT-PANIC-ABI.
Base: `a841af5f063a043cdabef9e70bc5defeeb68bf9f`.

## Scope and diagnosis

Release PR #2875 introduced the distinction between `T(text)` numeric parsing
and `text as T` single-character code-point conversion. The root subsequently
reconciled the older draft #2868 floating parser fix without discarding this
source-form distinction. This defect is inherited from the release code-point
failure path; it is not evidence that the older #2868 patch is equivalent to
the reconciled semantics.

`lower_text_code_point_cast` rejects character counts other than one. Its
mismatch block called `rt_panic` with one text operand and a one-parameter
signature. `src/runtime/runtime_native.c` declares
`void rt_panic(const uint8_t* msg_ptr, uint64_t msg_len)`. The absent length and
incorrect text representation violate that ABI on the failure path, risking
corrupted diagnostics or invalid memory reads instead of the intended panic.
This is a source-confirmed defect; no native reproduction was attempted in
this source-only reconciliation task.

The repair uses the same literal-pointer plus explicit-length lowering as
`lower_text_float_cast`: `emit_const_str`, message byte length, and a known
fixed `(ptr i8, i64) -> unit` signature. The existing Abort terminator remains.
Character counting, code-point extraction, numeric target conversion,
`ConvertCall` dispatch, and `T(text)` parsing are unchanged.

## Authored regression contracts

- `text_codepoint_cast.spl`: ASCII A, two-byte é, four-byte 😀, integer and
  floating destinations; `"7" as i64` is 55 while `i64("7")` is 7 and
  `f64("7")` is 7.0. Expect exit 0 and `TEXT_CODEPOINT_CAST_PASS`.
- `text_codepoint_cast_empty.spl`: empty text as i64 must exit nonzero, emit
  exactly the paired `.stderr` message, and never print the acceptance marker.
- `text_codepoint_cast_multiple.spl`: multi-character text as f64 has the same
  negative contract with its target-specific `.stderr` message.
- `text_codepoint_panic_abi_spec.spl`: real frontend/HIR/MIR lowering checks
  both diagnostic targets, call arity, argument constant identity and raw
  byte-pointer representation, explicit length, fixed signature, and Abort.

No authored regression execution or native PASS is claimed. Compiler
construction/native repair cycles are intentionally not started: the parent
lane exhausted its HIR serialization cycle cap. A future coordinated producer
must validate the positive ARM fixture, both exact stderr/nonzero negatives,
and genuine LLVM18 RISC-V objects (EM243); no RISC-V execution claim is planned.
Standalone-head SSpec and broader compiler/lib/MCP checks remain pending.
The original draft #2868 is not pushed, rewritten, merged, or admitted here.
