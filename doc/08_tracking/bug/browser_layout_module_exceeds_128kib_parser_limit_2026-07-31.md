# `simple_web_html_layout_renderer_layout.spl` exceeds the 128 KiB parser limit on main (2026-07-31)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
that found it.
**Guard:** `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl`,
example *"keeps every parser input below 128 KiB"*.

## Measurement

Limit is `128 * 1024` = 131,072 bytes.

| file | origin/main | verdict |
|---|---|---|
| `..._layout.spl` | **135,289** | **OVER by 4,217 B** |
| `..._paint_layout.spl` | 127,363 | under, 3,709 B of headroom |
| `..._core.spl` | 124,431 | under |
| `..._decl_apply.spl` | 110,534 | under — but see below |

`origin/main` is therefore already RED on this guard: the spec reports
`2 total, 1 passed, 1 failed` against a pristine checkout of the origin blob,
with no local changes at all.

## How it was found, and why it looked like a regression

A lane reported this spec at 2/2. That was true *for the lane*, because its
working copy of `layout.spl` was a stale, smaller generation. When the
coordinator 3-way merged the lane's 2 real lines onto origin's newer
`layout.spl` — which had grown by another session's RTL-flex and grid-alignment
work — the merged file inherited origin's size and the guard went red.

The regression is real but it is **origin's**, not the merge's. The merge adds
548 bytes on top of a file that was already 4,217 B over.

Confirmed by blob swap: restore the pure `origin/main` blob, run the spec, still
1/2.

## Two things worth acting on

1. **`layout.spl` needs splitting.** Do it as its own change, never bundled.
   A previous split attempt silently deleted 663 lines while self-reporting
   success — a split must ADD total bytes; if the byte count goes down, it was
   lossy. `module_split_spec` only checks per-file SIZE, so it cannot detect a
   split that drops code.
2. **`paint_layout.spl` has 3.7 KB of headroom and is growing.** It is the next
   file to cross the line. The text-decoration work landed earlier today
   consumed part of that margin.

Also note the guard checks 8 named files and does **not** include
`..._decl_apply.spl` (created after the spec was written), so that file is
currently unguarded at 110 KB.

## Re-measured 2026-08-10 — grown well past the original finding

```
150,915  simple_web_html_layout_renderer_layout.spl        (was 135,289)
155,941  simple_web_html_layout_renderer_core.spl           (was under)
165,305  simple_web_html_layout_renderer_paint_layout.spl   (was 127,363)
118,336  simple_web_html_layout_renderer_decl_apply.spl     (was 110,534, still unguarded)
125,999  simple_web_html_layout_renderer.spl                (new, near the line)
```

Three files are now over the 131,072-byte limit, not one, and the overage on
`_paint_layout.spl` alone is 34 KB. `_paint_layout.spl` is also currently
owned by another parallel agent session (do-not-touch list), so any split
touching it must be sequenced after that lane. Status stays
**ARCHITECTURAL-OPEN**: a correct fix is a dedicated, lossless module-split
change per file (verified by total-byte-count non-decrease, per the warning
above about a prior split that silently dropped 663 lines) — not something to
attempt inside a mixed bug-sweep pass. No code changed by this note.
