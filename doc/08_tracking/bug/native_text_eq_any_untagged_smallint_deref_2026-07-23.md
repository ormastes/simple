# native: rt_text_eq_any derefs untagged small-int as char* (SIGSEGV)

**Found:** 2026-07-23, MCP entry-closure rebuild campaign (repro W42).
**Status:** OPEN — not an MCP blocker (API-misuse input), but a robustness gap.

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
