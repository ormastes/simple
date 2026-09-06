# LSP MCP: integer position args (line/character) corrupted in deployed server

- **Status:** Open — root cause is a **`native-build` codegen/runtime bug**, not a `tools.spl` logic bug
- **Severity:** P1 (server currently fully unusable — see 2026-06-14 PM update)
- **Date:** 2026-06-14
- **Component:** `bin/simple native-build` codegen+runtime (`text.to_int()`, text `>=`, `str(negative i64)`); surfaces in `src/app/simple_lsp_mcp/`

---

## UPDATE 2026-06-14 (PM) — corrected root cause: native-build codegen, not tools.spl

The original write-up (below) blamed `tools.spl` UFCS resolution of `.to_int()`. That was
the right *suspicion* but the wrong *layer*. Diagnosis with minimal reproducers (built via
`bin/simple native-build`, compared native-vs-interpreter) shows the real causes are
**codegen/runtime bugs in primitive operations on the `native-build` path**, reproduced in
3-line programs with **no LSP code involved**.

### Confirmed minimal codegen bugs (native-build only; interpreter is correct)

1. **`text.to_int()` returns tagged garbage.** `"1".to_int()` → `<value:0x1>`,
   `"136".to_int()` → `17`. This *is* the originally-reported "integer position args
   corrupted": `line_raw.to_int()` produced garbage line numbers.
2. **Text `>=` comparison miscompiles.** `"5" >= "0"` → `false` (should be true);
   `"5" <= "9"` → `true` (correct). So `>=` specifically is broken; any digit test of the
   form `ch >= "0" and ch <= "9"` silently fails.
   Repro for (1)+(2): `doc/08_tracking/bug/repro/native_text_ordering_to_int_repro.spl`.
3. **`str(negative i64)` corrupts the value (display-only).** `str(-1)` →
   `2305843009213693951` = `0x1FFFFFFFFFFFFFFF` (`-1` with the top 3 bits masked — a NaN-box
   tag-extraction artifact). `-5`→`…FFB`, `-7`→`…FF9`. **Comparisons still work**
   (`if x < 0` branches correctly), so this is display-only and does **not** explain the
   empty-extraction symptom; it is a *separate* bug.
   Repro: `doc/08_tracking/bug/repro/native_str_negative_i64_repro.spl`.

Verify each: `bin/simple native-build --runtime-bundle core-c-bootstrap --entry <repro> --output /tmp/r && /tmp/r`,
then `bin/simple run <repro>` for the interpreter baseline. Reproduces identically under the
default bundle too, so it is the **codegen path**, not the runtime bundle.

### Scope: `native-build` path only, NOT native execution in general

`bin/simple` is itself a native binary — it calls `stack_text.to_int()` in its lexer to parse
every numeric literal and prints integers constantly, all correctly. So these ops are **not**
universally broken in native code; they are broken specifically in programs produced by
`bin/simple native-build` (the path that builds the MCP servers). `bin/simple` is built by the
**bootstrap** pipeline, which evidently emits a different i64 representation/runtime ABI than
`native-build`. The signature (`"1".to_int()`→`<value:0x1>`, `str(-1)`→`0x1FFF…FFF`) is a
**NaN-box-tagged value meeting code that expects a raw i64** — codegen and the linked runtime
disagreeing on i64 boxing in the `native-build` path. Fix should compare the failing
`native-build` i64 path against the working **bootstrap** one.

### Two distinct failures — only the total one is clearly a recent regression

- **Integer-arg corruption** (`.to_int()` etc.): the original matrix below already showed the
  integer tools broken on the Jun-13 binary while string tools worked → this was **likely
  already present** in `native-build`, not necessarily new.
- **Total failure** (all tools → `"Missing tool name"` / `tools/call` segfault): via the live
  `simple-lsp-mcp` client, **every** tool — including `lsp_symbols` — now returns
  `"Missing tool name"`; fresh control builds *segfault* on `tools/call`. The Jun-13 binary's
  `lsp_symbols` worked (per the prior session's matrix; that binary is gone, not re-tested), so
  *this* is the recent regression. **Not minimally reproduced.** Ruled out as its cause:
  cross-module returns (work), persistent init→loop heap state (works), the `--entry-closure`
  build closure (minimal closure builds work), and stubbed symbols on the arg path (only
  type/enum descriptors like `Option`, `JsonKind` are stubbed — the string *functions* are
  real). A faithful single-file replica of the server's read→parse→extract path **works**; only
  the full module graph fails. Bisect suspects (post-Jun-12 backend/resolve commits):
  `61b74d9132f` (M12-3b call-site default-arg fill), c-backend `val`-binding fixes,
  `b2e2889e052` — but confirm against a server rebuilt from that SHA.

### Fix status

- `tools.spl` parses line/character with a self-contained `arg_int_field` using **only `==`
  digit matching** (avoids both broken `.to_int()` and `>=`). Correct fix for the
  *integer-arg corruption*, unit-safe (its primitives are proven to compile correctly).
  **Cannot be end-to-end verified or deployed until the separate total-failure regression is
  fixed** — fresh server builds are broken regardless of this change (proven by a control
  build of unedited source that also segfaults).
- Real resolution: fix the `native-build` codegen/runtime i64-boxing bugs (#1/#2) and the
  total-failure regression. Until then, run the LSP MCP via the interpreted `.spl` path or
  revert the deployed binary to a pre-regression build.

---

## Symptom (original report)

Live MCP calls against the deployed `bin/release/.../simple_lsp_mcp_server`:

| Tool | Result |
|------|--------|
| `lsp_symbols` | ✅ works (fixed separately — entry-point) |
| `lsp_diagnostics` | ✅ works |
| `lsp_completion` | ✅ returns a list (but position-independent — see note) |
| `lsp_hover` | ⚠️ returns `null` |
| `lsp_definition` | ❌ `No symbol found at <file>:740116738` |
| `lsp_references` | ❌ `No symbol found at <file>:740323010` |
| `lsp_document_highlight` | ❌ `…:740537890` |
| `lsp_type_at` | ❌ `…:740743906` |
| `lsp_type_definition` | ❌ `…:740952898` |
| `lsp_implementation` | ❌ `…:741163762` |
| `lsp_signature_help` | ❌ `…:741865010` |

Split is exact: every tool that passes an integer `line`/`character` was broken; every
string-only tool worked. The garbage value was monotonically increasing across calls — a
growing pointer-/tag-like value, consistent with the `.to_int()` tagging bug confirmed above.

NOTE (2026-06-14 PM): the current deployed binary is worse — all tools (even `lsp_symbols`)
return `"Missing tool name"`. See the update section above.

## Where it surfaces

`src/app/simple_lsp_mcp/tools.spl::handle_tool_call` numeric path used `line_raw.to_int()` /
`char_raw.to_int()`, then `run_lsp_query` built `[..., str(line0 + 1), str(char0 + 1)]`. The
`.to_int()` calls return tagged garbage under `native-build` (see bug #1).

## Verification harness

```
# backend sanity (works directly):
bin/simple src/lib/nogc_sync_mut/lsp/lsp_query.spl definition src/lib/common/base_encoding.spl 17 4
# minimal codegen repros (native broken / interpret correct):
bin/simple native-build --runtime-bundle core-c-bootstrap --entry doc/08_tracking/bug/repro/native_text_ordering_to_int_repro.spl --output /tmp/r && /tmp/r
bin/simple run doc/08_tracking/bug/repro/native_text_ordering_to_int_repro.spl
```
