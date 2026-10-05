# Enum numeric runtime failures: Any cast and incorrect float constants

Status: Any-cast source repair candidate; native regression qualification UNRUN.
Float-constant corruption remains open and is not claimed fixed by this change.

Actual evidence: `diagnostic-authored-tests-p23bd20-1/results.json`, producer
3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb,
source e37658577b3279e30f1631dfcc8474d1c860511b. Cranelift compiled the original
`test/04_smoke/native_enum_numeric_payload_widths.spl` successfully, then ran
all 13 checks and exited 10. Signed i8, unsigned u8 and u64 passed; all remaining
float/mixed/Any/named/rewrapped checks failed. Run peak RSS was 9776 KiB.
Original stdout SHA256: b5e2a248f38dcfcafc07714ce75921ca3d0fcc83e0aa0ce71399a5cded145f6b.

The source-proven Any bug is in `lower_cast_expr`: its final numeric cast
operates on a tagged RuntimeValue's carrier without decoding it. Declared enum
Any extraction correctly remembers Any provenance, but the cast consumer
ignored it. Actual object imports include `rt_value_float`/`rt_value_as_u64`
and omit `rt_value_as_int_wide`/`rt_value_as_float`.

The fix requires semantic Any provenance and decodes integer/float/bool payloads
through the existing RuntimeValue boundary. Integer narrowing happens after
wide decoding, so a heap-boxed wide integer is not mistaken for an inline
tagged value. Ordinary scalar casts and nominal enum discriminant casts keep
their original routes. This adds no allocation, ownership transfer, copying or
mutation of the stored value; it invokes an existing read-only decoder. Runtime
memory and timing measurements on the repaired compiler are still required.

Three added MIR assertions test raw scalar exclusion, wide integer decoding
before narrowing, and f64/f32 decoder calls. The independent native fixture
`enum_any_numeric_cast/main.spl` has 12 checks spanning signed/unsigned widths,
tuple payloads, re-use of the original value, nested array/enum extraction,
f64/f32 and heap-wide-to-i8 narrowing. It derives floats from integer parameters
to isolate the cast bug; the original decimal-literal 13-check fixture remains
unchanged and must pass independently on both backends before closure.

The float failures have additional object evidence: `agrees` contains constants
0x427e5ce258bf1000 (2086517705713.0) and 0x427e5ce258f21000
(2086517706529.0), where source expects 2.25 and 1.5. Its extraction uses actual
bitcast/narrow instructions, so incorrect constants already reach codegen.
Boxed-float carrier conversion upstream is a hypothesis, not an assigned cause.
No out-of-bounds access, lifetime violation or alias mutation has been proved.
