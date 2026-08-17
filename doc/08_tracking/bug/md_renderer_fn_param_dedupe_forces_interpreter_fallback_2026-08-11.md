## RESOLVED (root cause removed) — re-verified 2026-08-17

The fn-typed callback parameter this bug is about no longer exists.
`src/lib/editor/render/md_renderer.spl:162` is now:

```
fn _mdr_render_for_tui(model: BlockModel, viewport_start: i64, viewport_height: i64, wiki_index: MdWikiIndex?) -> [text]
```

`grep -n 'render_block:' src/lib/editor/render/md_renderer.spl` returns nothing,
and both entrypoints (:202, :205) now pass a plain `MdWikiIndex?` (`nil` /
`Some(index)`) instead of a named function or a closure. With no lambda/closure
in the module, the reported bailout
("creates a lambda/closure; the JIT closure ABI does not tag-box lambda
arguments or results") can no longer be emitted for these functions. The dedupe
was kept; only the closure-shaped parameterization was replaced.

Runtime re-measurement is INCONCLUSIVE in this lane: a direct `bin/simple run`
probe could not construct a `BlockModel` (`unknown static method from_text`), so
no fresh JIT-vs-interpreter timing was taken. Closing on the source-level root
cause; reopen with a timing probe if the TUI render path is still slow.

# md_renderer TUI dedupe forces a whole-callee-tree interpreter fallback (~15x slower)

**Date:** 2026-08-11
**Status:** OPEN — output is correct, but both TUI render entrypoints lost JIT compilation.
**Commit:** `582ef0d69a39022302333894fa650e47b6845e85`
("refactor: dedupe TUI viewport-slicing loop in md_renderer")
**File:** `src/lib/editor/render/md_renderer.spl`
**Severity:** performance regression on a per-keystroke TUI render path.

---

## What the commit did

`md_render_blocks_for_tui` and `md_render_blocks_for_tui_with_wiki` contained an
identical ~30-line viewport-slicing walk. The commit extracted it into

```
fn _mdr_render_for_tui(model, viewport_start, viewport_height, render_block: fn(RenderBlock) -> [text]) -> [text]
```

parameterized by a function-typed callback. `md_render_blocks_for_tui` passes the
named function `md_render_block`; `md_render_blocks_for_tui_with_wiki` passes a
lambda closing over `index`.

## The refactor is output-correct

A/B verified by swapping the pre-change and post-change blobs into the same tree
and running the same probe (heading + paragraph + fenced code + list document;
`viewport_start` 0/3/6, `viewport_height` 0/2/4/6, negative start, start past end
of blocks, oversized height, and every one of the 4 blocks made active in turn,
against both entrypoints):

```
151 data lines OLD, 151 data lines NEW
diff old.data new.data  ->  *** DATA IDENTICAL OLD vs NEW ***
```

Which render function runs for active vs inactive blocks is unchanged: with block
2 (the fenced code block) active, both old and new emit the raw lines
`|```|code1|code2|``` `, and with it inactive both emit the SGR-styled
`|ESC[90m│ESC[0m code1|...`. Viewport slicing, the empty-viewport guards
(`viewport_height <= 0`, `viewport_start < 0`), and the cursor/window arithmetic
all produce identical results. The plain and wiki entrypoints agree with each
other in both versions.

## The defect: the fn-typed parameter kills JIT for BOTH callers

The post-change file emits a bailout the pre-change file does not:

```
[INFO] JIT compilation failed, falling back to interpreter:
  Cranelift JIT compile: Module error: function 'md_render_blocks_for_tui_with_wiki'
  creates a lambda/closure; the JIT closure ABI does not tag-box lambda arguments
  or results and is incompatible with the runtime's RuntimeClosure layout, so JIT
  would return wrong values or crash; deferring to interpreter
```

Bailout count: **OLD = 0, NEW = 1.**

Crucially the damage is **not confined to the lambda caller**. The plain
entrypoint passes a *named function reference*, not a closure, yet it degrades
just as badly, because the shared `_mdr_render_for_tui` it now calls is itself
un-JIT-able — the known "caller-module frame triggers silent interpreted fallback
of the whole callee tree" behavior.

Measured, same machine, same probe binary, 3000 iterations of
`md_render_blocks_for_tui(model, 0, 40)` (+ the same for the wiki variant):

| probe | OLD | NEW | ratio |
|---|---|---|---|
| plain entrypoint only | 0.454s | 6.635s | **14.6x slower** |
| plain + wiki entrypoints | 0.618s | 10.527s | **17.0x slower** |

Both versions print identical results (`PLAIN_DONE 27000`, `WIKI_DONE 27000`), so
this is purely the interpreter fallback, not extra work.

## Why this matters here

`md_render_blocks_for_tui*` is the markdown editor's TUI viewport render — it runs
on cursor movement and on every keystroke that changes the active block. A ~15x
regression on that path is user-visible latency, and it is silent: the bailout is
an `[INFO]` line, nothing fails, and no test in the tree covers it.

## Secondary gap

The commit added **no test**. Its message cites a standalone probe script
(`PARITY_OK` / `HEADING_OK` / `SLICE_OK`) that was not landed, so nothing in the
repo would catch a future regression of either the parity or the JIT-ability.

## Suggested fixes (not applied — this record is deliberately fix-free)

1. **Revert the parameterization, keep the dedupe another way.** Have
   `_mdr_render_for_tui` take a plain `use_wiki: bool` (plus an optional
   `MdWikiIndex`) and branch internally, instead of taking `fn(RenderBlock) -> [text]`.
   That removes both the closure and the fn-typed parameter, so both entrypoints
   should JIT again while the ~30 duplicated lines still live in one place.
2. Or accept the duplication and revert `582ef0d6` outright — 22 duplicated lines
   is cheap next to 15x on a keystroke path.
3. Either way, land a spec asserting parity between the two entrypoints on the
   boundary viewports above, so the next dedupe attempt is caught.

Fixing the underlying JIT closure ABI is the real cure but is far out of scope of
this refactor; option 1 is the local fix.

## Reproduction

```bash
# OLD vs NEW blob swapped into src/lib/editor/render/md_renderer.spl,
# probe calls both entrypoints in a loop, then:
grep -c "JIT compilation failed" old.txt   # 0
grep -c "JIT compilation failed" new.txt   # 1
```
