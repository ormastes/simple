# COLL rules walk top-level functions only, never methods

**Status:** OPEN 2026-09-19
**Area:** `src/compiler/35.semantics/lint/collection_patterns.spl`
  (the `module_get_decls()` / `DECL_FN` walk)

## Minimal reproduction

```
class Box:
    var items: [text]

    fn uniq(self) -> [text]:
        var seen: [text] = []
        for it in self.items:
            if not seen.contains(it):
                seen.push(it)
        seen

fn toplevel(xs: [text]) -> [text]:
    var seen: [text] = []
    for x in xs:
        if not seen.contains(x):
            seen.push(x)
    seen
```

```
$ bin/simple lint method.spl
method.spl:14:9: warning[COLL020]: manual dedup loop ...
Found 0 error(s), 1 warning(s)
```

Line 14 is `toplevel`. The method body is byte-for-byte the same idiom and is
reported nowhere. The rules iterate the module's top-level declarations and
descend into `DECL_FN` bodies; a `fn` inside a `class`/`impl` is not one of
those, so it is never visited.

## Scope

This is not COLL-specific in shape — any rule written against that same
top-level walk inherits it — but it is filed against the COLL family because
that is where it was measured.

Two of the 54 genuinely-quadratic dedup sites in the measured corpus are
methods and are silent for this reason:
`src/lib/nogc_sync_mut/database/feature.spl:343` (`fn all_categories`) and
`src/lib/nogc_sync_mut/database/fts_lexical.spl:185`. Both are textbook
single-statement dedup loops that the widened matcher would otherwise report.

## Fix

Descend into method declarations wherever the walk enumerates `DECL_FN`. The
fix side needs no change: `collection_fix_proofs` reasons per function body
and would receive method bodies on the same footing. Worth re-running the
coverage measurement afterwards, since this is a pure gain — it can only add
diagnostics, never suppress one.
