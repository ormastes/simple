# Geometry differ: list items are reparented, desyncing every later nth-path

- status: OPEN
- area: app / chrome_showcase geometry differ + browser_engine Draw IR parentage
- found: 2026-09-13, Chrome parity round 6
- files: `src/app/ui/chrome_showcase/layout_geometry_diff.spl` (keying),
  Draw IR parent attribution in the browser-engine emit path

## Symptom

`sh scripts/check/check-chrome-layout-geometry-diff.shs` with
`GEOM_DIFF_HEIGHT=20000` reports, on `origin/main` @ `d522cc98da2`:

| page | compared | mismatched |
|---|---|---|
| html | 253 | 247 |
| animation | 81 | 79 |
| css-paint | 493 | 492 |

`html` additionally reports 178 elements missing in Simple and 179 Simple-only
boxes. That is not 178 real layout defects: it is ONE structural divergence
cascading through the ordinal keying.

## Root

Both sides key an element by its ordinal path relative to `<body>`. Chrome's
walker, on `html.html`, sees `path:0/0/4` = `<section>` with exactly THREE
children — `0/0/4/0(h3)`, `0/0/4/1(p)`, `0/0/4/2(ul)` — and the list items
below the `<ul>`. The Simple side emits `0/0/4/3(p)`, `0/0/4/4(li)`,
`0/0/4/5(li)`, ... : the `<li>`s are attributed to the SECTION, not to the
`<ul>`. `_path_key` (`layout_geometry_diff.spl:127-159`) builds the key by
walking the parent/ordinal columns that come off the Draw IR commands, so a
wrong parent on the wire becomes a wrong key, and every sibling after the
first reparented node shifts by one.

Once the ordinals shift, every later element is reported both "missing in
Chrome" and "missing in Simple", and the per-feature mismatch clusters below
that point are noise.

## Consequence for round 6 and after

The differ's per-feature ranking is only trustworthy DOWN TO the first
reparented node. On `html` that is `path:0/0/4/3`, item 3 of 253, so the
"what ranks next" question the round-6 brief asks cannot be answered from this
report. The four root mismatches above the desync are real and were used:
`main` dh 376, `article` dh 16, `h3` dw 6, `dl`/`p` dy 17.

Not fixed here: both candidate owners (Draw IR parent attribution, and the
differ's keying) are outside the round-6 file set, and a fix must decide which
side is wrong — Chrome's walker is the oracle, so the Draw IR parentage is the
likelier defect. Until then, prefer the PIXEL differ
(`check-chrome-catalog-pixel-diff.shs`) for ranking pages, and use the
geometry differ only for the boxes above the first desync.

## Round 8 (2026-09-13) — candidate (ii) established by construction; candidate (i) is not the cause

Round 7 left two candidates and established neither. Reading
`src/app/ui/chrome_showcase/layout_geometry_diff.spl:185-215` settles it without
needing another render:

The Simple side's node list is built **only from Draw IR COMMANDS** —

```
while i < commands.len():
    val c = commands[i]
    val tag = _style_value(c, "tag")
    if tag != "" and _layout_tag(tag) and not _seen(ids, c.component_id):
        ids.push(c.component_id)
        parents.push(c.parent_id)
```

so an element that emits no command at all never enters `ids`. A `<ul>` with no
background, border or marker of its own paints nothing, therefore emits nothing,
therefore is **absent from the Simple side's element list** — while the Chrome
side walks the DOM and includes it (same `_layout_tag` predicate, but over
elements, not over paint). The `<li>`'s recorded `parent_id` then names a node
the list does not contain, and the path resolves against the nearest ancestor
that IS present: the enclosing `<section>`. That is exactly the reported
symptom.

This is candidate **(ii)**, and it is a property of the differ's own list
construction rather than a guess. Candidate (i) — "the parsed tree really does
give the `<li>` the `<section>` as parent" — is correspondingly NOT the cause:
the emitter copies `nodes[i].parent` faithfully
(`..._paint_layout.spl:3117-3125`, as round 7 already established), and the
parent it copies is the `<ul>`; the id simply has no row on the Simple side.

**Not fixed in round 8.** The fix is a change of kind, not a patch: the Simple
side must enumerate LAID-OUT ELEMENTS (the layout tree), not painted commands,
so that paintless ancestors keep their ordinal slot — the same basis the Chrome
walker already uses. Doing that inside the differ risks changing every page's
key scheme at once, so it wants its own lane with a before/after on all eight
pages. Until then the `html` and `css-layout` reports stay desynced after the
first paintless intermediate ancestor, and their absolute mismatch counts are
inflated by it.
