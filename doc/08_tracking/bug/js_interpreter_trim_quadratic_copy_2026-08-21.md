# JS interpreter trim quadratic reconstruction

**Status:** FIXED
**Found:** 2026-08-21
**Owner:** Pure-Simple JavaScript interpreter

## Defect

`trim`, `trimStart`, and `trimEnd` in
the `nogc_sync_mut`, `nogc_async_mut`, and `gc_async_mut` JavaScript
interpreter string-method modules rebuilt the
retained text one character at a time with `result = result + str_val[i]`.
Immutable concatenation copies the retained prefix on every iteration, making
an N-character result perform `N*(N+1)/2` bytes of copy work and transient
allocation. At N=20,000 that is 200,010,000 copied bytes.

The repository's retained primitive benchmark in
`rt_string_concat_quadratic_2026-06-12.md` measured 20,000 naive concatenations
at 2.768 seconds versus 5.3 milliseconds for linear construction (521.6x).

## Fix

After locating the unchanged trim boundaries, the runtime-family-neutral
`common.js.engine.string_trim.js_trim_text` returns one `text.slice` result.
All three ownership-family interpreters route their three trim branches to it.
This preserves the existing whitespace definition and output while reducing
result reconstruction to one allocation and O(N) copied bytes. Boundary scans
use byte offsets, matching `text.len()` and `text.slice`; this also avoids the
old end-index mismatch on UTF-8 input while preserving non-whitespace bytes.

## Evidence

- `browser_session_string_trim_spec.spl`: actual `JsRuntime.eval` dispatch for
  empty, all-whitespace, ASCII boundary, and UTF-8 behavior of all methods.
- `js_string_trim_copy_work_contract_spec.spl`: deterministic guard requiring
  direct slicing in all ownership variants, plus measured 20k-to-40k scaling.

Focused seed-stage measurement (32 calls each): 20,000-byte input 1,456 us;
40,000-byte input 1,323 us; checksum 1,920,000. The bounded contract requires
the 2N row to remain below `3*N + 5 ms`, excluding quadratic reconstruction.
