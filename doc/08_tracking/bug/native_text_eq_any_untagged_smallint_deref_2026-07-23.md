# native: rt_text_eq_any derefs untagged small-int as char* (SIGSEGV)
## Closed 2026-09-16 — ## Fix section: rt_interp_cstr/rt_text_eq_any hardened; SOURCE-FIXED status

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Found:** 2026-07-23, MCP entry-closure rebuild campaign (repro W42).
**Status:** SOURCE-FIXED — focused hosted-runtime check added; bootstrap replay pending.

## Symptom
Native binary SIGSEGVs at fault address exactly `value << 3` when a text
equality (`==`) receives a boxed small int where text was expected:

```simple
use std.common.json.{json_array_get}
fn main() -> i64:
    val v = json_array_get([41], 0)   # raw array, NOT a json ("array", …) tuple
    return 30
```

`json_get_type` does `value.0` (tuple-index on what is actually a raw array →
element 0, boxed 41 = 0x148) then `== "array"`. Native lowers this to
`rt_text_eq_any(0x148, "array")`; 0x148 has clear low tag bits, so it is
treated as a raw `char*` and strlen/strcmp derefs it → SIGSEGV at 0x148.
Interpreter path returns false gracefully for the same input.

## Expected
`rt_text_eq_any` should range-check candidate pointers (or the boxed-int tag
scheme must be distinguishable from heap pointers) and return false instead of
dereferencing. Interp/native divergence on garbage-in is a silent-crash channel
for `any`-typed library code (std.common.json takes `any` everywhere).

## Notes
- Root overlap with the known seed "BoxInt <<3 mangles enum heap-handles" class
  (see memory project_stage4_wall_and_hardening): `41<<3 = 0x148` is
  indistinguishable from an aligned low heap pointer.
- Fix direction: `rt_interp_cstr`/`rt_text_eq_any` reject candidates below the
  minimum mmap address (e.g. `< 0x10000`) as non-pointers.

## Fix

`rt_interp_cstr` now rejects signed values below `0x10000`, covering both
positive and negative boxed small integers before any C-string dereference.
`rt_text_eq_any` validates both normalized operands before pointer equality.
The focused native-runtime test checks the original `41 << 3` case in both
operand orders.


## Verification note (2026-11-25, P2 ledger sweep)

STALE-CLOSED confirmed by code inspection. `rt_interp_cstr`
(`src/runtime/runtime_native.c:4846-4850`) rejects signed candidates below
`0x10000` (`int64_t` compare, so negative boxed ints are covered too) before
any C-string dereference, and the focused native-runtime check
`src/runtime/test/rt_text_eq_any_untagged_smallint_selfcheck.c` exercises the
original `41 << 3 = 0x148` case in both operand orders (probes P2/P3) plus
the equal-smallint case (P4). Running the selfcheck needs a hosted runtime
build, which is not available on this Windows host; closure rests on the
2026-09-16 classification plus this source check. Kept closed.
