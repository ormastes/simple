# riscv64 in-guest component rows lose string CONTENT (mcp / caret / testrun)

Status: OPEN
Arch: riscv64 freestanding (SimpleOS, OpenSBI `-bios fw_payload`)
Gate: `scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs`
Filed: 2026-08-31

## What this is NOT

It is not the closure runtime, and it is not a trap. Both of those were the
previously-reported riscv64 blockers and both are now measured fixed:

* The four `rt_closure_*` symbols are `T` (strong) in `kernel.elf`, and the mcp
  dispatcher demonstrably **calls the handler closure**: it produces a
  well-formed `{"status":"ok","body":...}` envelope for the registered tool and
  correctly refuses the unregistered one with
  `{"status":"error","code":"unregistered_tool","reason":"no handler for:
  no_such_tool_xyz"}`. A nil or missing allocator cannot produce either line.
* The guest no longer traps. The earlier trap — OpenSBI banner appearing once in
  a 373,249-line log — was `-> ()` functions compiling to a terminating `ud2`
  with no `ret` (fixed in the hir type-resolver: an empty `Type::Tuple` now
  resolves to `TypeId::VOID`). All four rows now run to completion and the guest
  parks cleanly; the serial log is 86 lines.

## The residual defect

Three of the four rows fail on string CONTENT while their control flow is
correct. From `build/os/riscv64_components/serial.log`:

```
[mcp] request  tool=echo args=[MCP_RTT_PAYLOAD]
[mcp] response {"status":"ok","body":"

"}
[mcp] FAIL registered dispatch lost the payload
[caret] built message: {"role":"user","content":"CARET_RTT_CONTENT"}
[caret] extracted role=user
[caret] extracted content=
[testrun] FAIL parser did not report passed=2
```

`caret` extracts `role` correctly but `content` empty; `mcp`'s echoed body is
empty where the request line shows the payload present; `testrun`'s parser counts
nothing. `devtool` — the one row that does not accumulate or scan a string — is
green.

## Ruled out so far

* `rt_index_get` returning NIL for a text receiver. This was real and IS fixed
  (riscv64 handled only `HEAP_ARRAY`; both siblings dispatch `HEAP_STRING`), but
  rebuilding with the fix produced a **byte-identical** transcript, so `text[i]`
  is not reaching `rt_index_get` on this lane. Kept anyway: it was a genuine
  divergence from both siblings.
* Missing or weak symbols. `nm kernel.elf` reports **zero** `U` or `W` entries;
  every string primitive (`rt_string_concat`, `rt_string_builder_*`,
  `rt_string_bytes`, `rt_bytes_to_text`, `rt_string_char_at`, `rt_array_get`,
  `rt_len`) is defined `T`. This is a semantic defect in one of them, not a
  stub-fallback.
* Heap exhaustion. `g_heap` is 1 MiB (`baremetal_runtime_core.inc.c:78`); a stale
  comment elsewhere in that file still says 64 KiB.

## Next step

Needs an in-guest probe kernel, not more source reading: print the length and
first bytes after each stage of `_echo_handler`'s `s = s + a` accumulation
(`for` element fetch -> concat/builder -> `.bytes()` -> `rt_bytes_to_text`) to
find which stage first reports zero. The same probe answers caret's
`extract_json_string`, since both rows fail the same way.

Cross-arch reference: the identical product code round-trips green on x86_64
(`COMPONENT_MCP_SIMPLEOS_X86_64_OK`) and aarch64, so the defect is in this
runtime's own string implementation, not in the component or the compiler.
