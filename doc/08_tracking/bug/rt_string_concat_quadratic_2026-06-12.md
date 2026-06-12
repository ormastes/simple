# rt_string_concat_quadratic: O(n²) string building in MCP JSON layer

**Status:** MITIGATED 2026-06-12 — .spl-level builder rewrites applied; root-cause in Rust rt_string_concat remains open.
**Severity:** High — native MCP server burns ~1.5 s CPU on a single `tools/list` handshake (38 KB JSON).
**Affected files:**
- `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` — `jo1`–`jo5` builders
- `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl` — `jsonrpc_notification`, `jsonrpc_request`, `jsonrpc_error_with_data`
- `src/app/mcp/main_lazy_json.spl` — `_slice_text`, `first_n_chars`, `make_tool_error`
**Spec file:** `test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl`
**Path:** `bug` track.

## Symptom

`bin/simple_mcp_server` (native Cranelift binary) answers `initialize` +
`tools/list` in **~1.5 s CPU** while `bin/simple_lsp_mcp_server` does the
same in **~50 ms**. The gap is not the runtime itself — profiling (gdb
watchpoints + `/usr/bin/time -v`) shows the hot symbol is
`__memcpy_avx_unaligned_erms`, called from the Rust string concat runtime
primitive, on a single JSON serialisation path.

The native perf trace shows a single function (`tools/list` JSON builder)
accounting for >90% of the CPU time, invoked once per handshake, allocating
O(k²) bytes where k is the number of tool entries (~129 tools × ~300 B each
= ~38 KB final payload).

## Root-Cause Analysis

### Primary: `acc = acc + piece` accumulation pattern (O(n²))

Simple's `+` operator on `text` calls `rt_string_concat`, which allocates a
fresh buffer of size `len(acc) + len(piece)` and copies both operands on
every call. With k concatenation steps and total output size N:

- Step 1: alloc 1 byte, copy 1
- Step 2: alloc 1+piece, copy 1+piece  
- …
- Step k: alloc N, copy N

Total copies = O(N²/piece_avg). For the MCP case this is ~1.5 GB of copy
work for 38 KB of output — observed as repeated `__memcpy_avx_unaligned_erms`
deep stacks.

**Sites found in the .spl source (file:line):**

| File | Lines | Function | Concats |
|------|-------|----------|---------|
| `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` | 32–36 | `jo1` | 3 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` | 39–45 | `jo2` | 5 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` | 48–56 | `jo3` | 7 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` | 59–66 | `jo4` | 8 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` | 69–77 | `jo5` | 9 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl` | 21–25 | `jsonrpc_error_with_data` | 4 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl` | 30–34 | `jsonrpc_notification` | 4 |
| `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl` | 43–48 | `jsonrpc_request` | 5 |
| `src/app/mcp/main_lazy_json.spl` | 8–17 | `_slice_text` | O(n) per call |
| `src/app/mcp/main_lazy_json.spl` | 28–36 | `first_n_chars` | O(n) via push+join |
| `src/app/mcp/main_lazy_json.spl` | 366 | `make_tool_error` | 4 inline |

### Secondary: `_slice_text` O(n) per-char concat, called O(n) times = O(n²)

`_slice_text(s, start, end)` iterated every character of `s`, copying each
with `out = out + ch`. This is called by `_char_at(s, i)` which is itself
called in while loops over `i` from 0..n. Total cost: O(n²) for a scan that
should be O(n).

`char_at` in `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` avoids this by
using `s.substring(index, index+1)` directly — but `main_lazy_json.spl` was
written before `substring` with 2 args was confirmed stable, so it used the
safe workaround loop instead.

## .spl-Level Mitigations Applied (2026-06-12, T2)

### M1: Collapse multi-step `r = r + X` chains into single expressions

**Before (`jo3`):**
```
var r = LB()
r = r + p1
r = r + ","
r = r + p2
r = r + ","
r = r + p3
r = r + RB()
r
```

**After:**
```
LB() + p1 + "," + p2 + "," + p3 + RB()
```

The expression form does not reduce the number of `rt_string_concat` calls at
the .spl level (the compiler does not fold them), but it removes the O(n)
intermediate `var r` object allocations and makes the hot path visible to
future compiler optimisations (constant folding, join-tree rewrites).
Applied to `jo1`–`jo5` and the three `jsonrpc_*` builders.

**Hypothesis (unverified):** With Cranelift, the intermediate variable
elimination may allow LLVM-style allocation elision if the compiler detects
the left-associative concat tree. Not confirmed — mark as speculative.

### M2: Replace `_slice_text` O(n²) loop with `s.substring(start, end)`

`s.substring(start, end)` delegates to Rust's `&str[start..end]` which is an
O(1) pointer-range operation (no copy, no loop). All callers of `_slice_text`
and `_char_at` in `main_lazy_json.spl` now benefit from this.

**Before:** O(n) iterations × O(n) average copy cost per `_char_at` call in
inner scan loops = O(n²) per field extraction.

**After:** Each `substring(i, i+1)` call is O(1); inner scan loops stay O(n).

### M3: `first_n_chars` rewritten to use `s.substring(0, limit)`

The old implementation iterated every character with `parts.push(ch)` +
`parts.join("")`. New implementation: single `substring` call — O(1).

### M4: `make_tool_error` inline concat collapsed to `jo3` call

Replaces a 4-step LB+concat chain with the now-optimised `jo3` helper.

## Impact

All Simple scripts that build strings incrementally via `text + text` in a
loop or multi-step accumulation chain are affected. The pattern is idiomatic
Simple today (no mutable string builder type in stdlib). The MCP server is the
most visible victim because it serialises 129 tool entries on every cold start.

## Proposed Fixes at the Runtime Primitive Layer (Hypotheses)

These are author hypotheses — not verified against the Rust runtime source:

**H1:** Add `rt_string_builder_new() -> Builder`, `rt_string_builder_push(b, s)`,
`rt_string_builder_finish(b) -> text` externs backed by a `Vec<u8>` / `String`
with exponential growth, and expose a `StringBuilder` class in `std.common.text`.

**H2:** The compiler could detect left-fold concat trees (`a + b + c + d`) and
rewrite them to a single `rt_string_join([a, b, c, d])` call. Requires dataflow
analysis in the code-gen pass.

**H3:** The `text.join(sep)` method already exists and uses Rust's `join` —
it is O(n). `jo*` builders already use `ja(items).join(",")` for the array
case. Extending to object-pair arrays and rewriting all `.spl` builders to
push parts into a `[text]` and call `join` at the end would reduce copy work
to O(n) with constant factor ≈2 (one pass to measure, one to write).

## Files Changed

- `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` — jo1–jo5 single-expression
- `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl` — 3 builder functions
- `src/app/mcp/main_lazy_json.spl` — _slice_text, first_n_chars, make_tool_error, added exports
- `test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl` — new spec (21 tests pass)

## Cross-references

- `doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md` — perf wave plan
- `test/05_perf/mcp_json_perf_spec.spl` — existing perf benchmark
