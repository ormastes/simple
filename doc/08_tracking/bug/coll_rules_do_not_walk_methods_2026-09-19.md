# COLL rules walk top-level functions only, never methods

**Status:** RESOLVED 2026-09-19 — methods are walked via `coll_all_decls`
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

## RESOLVED 2026-09-19

`coll_all_decls` flattens nested declarations through `flat_decl_child_decls`
and all 12 rule loops iterate it. The reproduction above now reports both
sites (`method.spl:7:13` for the method, `:14:9` for the free function).
Diagnostic coverage over the 52-file sample moved 37 -> 40 of 68. As predicted
in this record it was worth more than the 2 sites it first showed up as,
though the sample is still mostly free functions, so the gain on
method-heavy code will be larger than 3.

Pinned by `collection_frame_rules_spec`, including an example asserting a
method and a free function with the same idiom report exactly twice — a
declaration reachable by two paths must not double-count.
