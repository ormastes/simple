# `use lib.gc_async_mut.gpu.browser_engine...` import alias fails to resolve `_web_budget_clock` module var — `std.` alias works fine

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Filed:** 2026-08-08
**Severity:** medium — blocks any spec/script that reaches
`simple_web_html_layout_renderer` through the `lib.` import alias; the `std.`
alias is a full workaround with no functional loss, so nothing is silently
wrong-but-green, but it is a real interpreter/module-loading gap on a
documented-preferred import path.

## Repro

```
use lib.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{simple_web_layout_debug_layout_by_id}

fn main():
    print(simple_web_layout_debug_layout_by_id("<div></div>", 100, 100, "x", "y"))
```

Run via either `bin/simple run <file>` or `bin/simple test <spec-using-this-import>`:

```
error: semantic: variable `_web_budget_clock` not found
```

`_web_budget_clock` is a module-level `var` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl`:

```
var _web_budget_clock: FrameClock = default_frame_clock()
```

Changing only the import line's alias from `lib.` to `std.` (same dotted path
otherwise) makes the identical program/spec run cleanly and produce correct
values:

```
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{simple_web_layout_debug_layout_by_id}
```

## Impact observed

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl`
  (pre-existing, not written by this change) imports via the `lib.` alias and
  is currently **red** under `bin/simple test` in this environment for exactly
  this reason (`3 examples, 3 failures`, all `_web_budget_clock` not found) —
  unrelated to any flex-grow logic defect.
- The new regression spec added alongside this bug report,
  `simple_web_margin_collapse_negative_spec.spl`, uses the `std.` alias and
  passes cleanly (`2 examples, 0 failures`).

## Suspected root cause (not confirmed)

`std.X` and `lib.X` likely resolve to the same file on disk but may be treated
as two distinct module instances by the loader/interpreter used by the
deployed seed binary (`bin/release/x86_64-unknown-linux-gnu/simple`,
currently a bootstrap-seed build per its own startup banner, not the
self-hosted binary). If so, a module-level `var` initialized under one loaded
instance would not be visible to code compiled against the other instance's
symbol table — consistent with warnings seen in the same test runs about
"co-compiled definitions with differing signatures" for unrelated public
functions (`dir_remove_all`, `file_read_bytes`, `shell`), which point at the
same class of duplicate-module-instantiation issue elsewhere in the tree.

## Unblock condition

Rebuild and redeploy the self-hosted binary (`bin/simple build bootstrap` then
redeploy per `.claude/rules/bootstrap.md`) and re-run both import forms; if
`lib.` resolves cleanly there, this was seed-specific and can be closed as
"self-hosted binary supersedes it". If it still fails under the self-hosted
binary, the module-loader dedup logic needs the actual fix.

## Workaround

Use `std.gc_async_mut.gpu.browser_engine....` (not `lib....`) for any new spec
or script that reaches into `simple_web_html_layout_renderer` and its
foundation module.

## Triage 2026-08-17 (lane m7c_lib_async) — LIVE resolver defect, workaround in place

`simple_web_html_layout_renderer_foundation.spl` declares the module var at
:32 (`var _web_budget_clock: FrameClock = default_frame_clock()`) and reads it
at :266, :299, :332. Every `use` in that file (lines 3-13) is the `std.` form;
no `use lib.` alias remains. So the *workaround* is what is in the tree — the
`lib.`-alias resolution defect itself is unfixed and lives in the compiler's
module resolver, not in this stdlib file. Not actionable from `src/lib/**`.
