# Result boolean and array unwrap payloads rejected

Status: source repair; native validation UNRUN.

The frozen 916be producer rejects the typed helper fixture twice with
`unsupported Result unwrap payload type`. Its `lower_result_unwrap` accepts
i64, f64, text, named struct/class and nested Result payloads but not Bool or
Array. The fixture unwraps both `Result<[i64], text>` and `Result<bool, text>`.
The flat diagnostic span `3:15` does not identify either real call site.
This is production-relevant: process_ops digest returns `Result<[u8], text>`
and callers unwrap it. The original Cranelift fixture instead failed SCV
admission; that independent failure is not evidence for this MIR defect.

The repair admits direct unwrap/unwrap_err Bool and Array payloads. Bool uses
the existing semantic enum payload decoder, which recognizes native true=1
and runtime true=11 without confusing false with absence. Arrays retain the
runtime handle, declared HIR array type, element MIR type and runtime-array
markers. Indexing and ordinary local value-copy rules remain responsible for
element decoding and alias isolation. No array contents are newly traversed,
copied, released or stored outside the existing per-function metadata owner.

The existing discriminant branch and opposite-variant panic are unchanged.
Nullable `.ok`/`.err` projections and unwrap-with-default use the shared helper
with a non-nil fallback; these new cases deliberately do not widen that path,
whose nil representation needs separate typed-result handling.

Regression sources:
- MIR specs inspect successful lowering, runtime array operations, payload
  extraction and the correct panic for unwrap and unwrap_err.
- Native positive fixture covers true/false, array indexing/length, empty array,
  error-array unwrapping and independent copies from the same Result payload.
- Two negative native fixtures must panic on Err unwrap and never reach their
  FAIL marker/exit99. A nonzero exit alone is insufficient proof: require the
  standard unwrap panic message and closed process receipts.

All new executable tests are UNRUN. Validate both native backends using a
coordinated producer containing this repair, preserving the current frozen
producer and caches. No bootstrap restart is requested by this checkpoint.
Memory/alias checks are in the positive fixture; elapsed time and peak RSS must
be captured during its native run. The source adds only bounded scalar decode
and per-local metadata, not runtime deep copies. No measured performance or
memory improvement is claimed.
