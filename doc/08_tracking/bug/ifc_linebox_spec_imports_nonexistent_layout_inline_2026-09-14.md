# `ifc_linebox_spec` is 0/10 — it imports a `layout_inline` that has never existed

- **Filed:** 2026-09-14 (web ↔ Chrome layout-geometry parity, round 18)
- **Status:** OPEN, pre-existing, NOT caused by round 18
- **Spec:** `test/01_unit/browser_engine/ifc_linebox_spec.spl`
- **Symptom:** all 10 examples fail with the same non-assertion error,
  `semantic: function \`layout_inline\` not found`. No `expected X to equal Y`
  line is ever produced, because no example reaches an assertion.

## What it is

The spec imports `layout_inline` from
`std.gc_async_mut.gpu.browser_engine.layout`:

```
use std.gc_async_mut.gpu.browser_engine.layout.{ ... }
```

No such function is defined anywhere under
`src/lib/gc_async_mut/gpu/browser_engine/`. Verified two ways:

```
/usr/bin/grep -rn 'fn layout_inline' src/lib/gc_async_mut/gpu/browser_engine/   -> 0 hits
git show HEAD:src/lib/.../layout.spl | grep -c 'fn layout_inline'               -> 0
```

The second command is the one that matters: the symbol is absent at the
COMMITTED tree, not merely in a dirty working copy, so this is not a local
breakage and not a regression from any uncommitted edit.

## Why it is being filed now rather than fixed

Round 18 touched `layout.spl` only to widen `_m14_is_inline_tag` by five tags
(+5 lines, −1). That change cannot produce a missing-symbol error, and the
`git show HEAD` probe above establishes the red predates it. The spec was run
as a neighbour check, which is how it surfaced.

Ten examples have therefore been reporting a *load* failure rather than any
behaviour for as long as the import has been wrong. That is worse than an
ordinary red: the spec names real inline-formatting-context invariants
(line-box count, baseline offset, `word-break: break-all`, `overflow-wrap:
break-word`, `text-align` fragment x) and none of them is being checked, while
the file's presence in `test/01_unit/browser_engine/` implies they are.

## Unblock condition

One of two, and the choice is an owner decision rather than a guess:

1. If the M14 public layout API is meant to expose an inline entry point, add
   `fn layout_inline` to `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`
   with the signature the spec already calls, and let the ten assertions run
   for the first time.
2. If the intended entry point is one that already exists (the spec's sibling
   `anonymous_block_spec.spl` drives `layout.spl` successfully, 4/4), repoint
   the import and re-derive the expected values against Chrome — they have
   never been validated against a running implementation.

Do NOT "fix" this by deleting the spec or marking it pending: per
`.claude/rules/testing.md`, a correct spec that fails is a legitimate artifact,
and this one fails for a mechanical reason that hides ten real invariants.
