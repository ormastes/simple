# `s[i].to_i64()` on a string-indexed char silently returns 0 — family census

**Filed:** 2026-08-10
**Parent:** `blink_selector_engine_totally_red_and_dom_node_builder_missing_2026-08-10.md` (Defect 2)
**Status:** OPEN — one consumer fixed (`src/lib/blink/css_parser/selector.spl`), family untriaged.

## Defect

On the interpreter lane, indexing a **String** and calling `.to_i64()` returns
**0 for every character**, with no diagnostic:

```
val s = "div"
print(s[0].to_i64())       # 0     <-- WRONG
print(s.char_code_at(0))   # 100   <-- correct
```

Any char-classification code using this pattern treats every byte as NUL and
produces garbage silently. `char_code_at(i)` is the correct call.

## Family size (raw census, 2026-08-10)

Pattern `\[[A-Za-z_0-9 +\-]+\]\.to_i64\(\)` over `src/lib` (via `/usr/bin/grep`,
vendor excluded):

- **454 sites in 119 files.**

**CAUTION — the raw count overcounts.** Many hits index a `[u8]`/`[i64]` list
(e.g. compress/, crypto/, hpack/), where `.to_i64()` on the element is a
widening no-op and NOT affected. The dangerous subset is only where the indexed
receiver is a **String/text**. Grep cannot separate the two; triage needs type
information (LSP `lsp_type_at` or a compiler-assisted sweep). Heavy suspects
(string-parsing modules): `common/sdn/parser.spl`, `common/encoding/base58.spl`,
`common/web/browser_renderer_protocol.spl` (36 hits),
`gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer*.spl`,
`nogc_*/net/telnet.spl`, `nogc_sync_mut/mcp_sdk/core/json.spl`.

## Fixed so far

- `src/lib/blink/css_parser/selector.spl` — all 8 string-index sites converted
  to `char_code_at`; sabotage-verified (reverting one site flips the two
  combinator examples in `css_selector_spec.spl` RED).

## Language-level fix (the real one)

`.to_i64()` on an indexed char should either return the code point or be a
compile/runtime error. Silently returning 0 is the worst option. Until then,
consider a lint/fence for `<string-typed>[i].to_i64()` once type-aware scanning
is available.
