# JIT: `if val` on `f64?`, `Option<f32>`, `Option<u64>` yields garbage

- **Date:** 2026-11-06
- **Status:** open (pre-existing; 81a4145fbce fixed only `Option<f64>`)
- **Severity:** P2 (wrong value)
- **Area:** `hir/lower/stmt_lowering.rs` `optional_enum_payload_inner`, MIR `rt_unwrap_or_self` decode

## Defect

JIT `if val x = <f64? | Option<f32> | Option<u64>>` binds a raw/tagged word instead of the
payload. `Option<f32> ?? 7.0` also prints a raw word. `Option<u64> ?? 0` prints 5 but
`a + 1` prints `<invalid-heap:0x29>` (same on the pre-fix binary). `Option<u64>` was excluded
from the `??` payload fix in 81a4145fbce on purpose (it printed 40, still tagged).
