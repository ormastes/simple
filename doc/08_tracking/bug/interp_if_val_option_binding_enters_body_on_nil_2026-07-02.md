# Interpreter: `if val x = <Option-returning fn>:` enters the body when the result is nil

Date: 2026-07-02
Status: source fixed 2026-07-15; executable interpreter proof pending a
runnable pure-Simple compiler artifact
Severity: P2 (silently wrong control flow; workaround exists)
Found by: W4b lane agent (browser link-click navigation work)

## Symptom

An `if val` binding over a function returning `BeDomNode?` executes the body
even when the function returns `nil`, binding the raw Option value instead of
the unwrapped payload. Field access inside the body then dies with:

```
error: semantic: undefined field: unknown property or method 'attributes' on Option
```

## Repro

In a `src/lib` module (observed in
`src/lib/gc_async_mut/web/simple_browser_page.spl`, interpreter path via the
deployed self-hosted binary):

```
fn hit(layout: BeLayoutBox, dom: BeDomNode, x: f64, y: f64) -> text:
    if val anchor = hit_test_anchor(layout, dom, x, y):   # returns nil here
        return be_dom_get_attr(anchor, "href")            # body still runs
    ""
```

Calling with a point outside every anchor box (nil result) enters the body and
crashes on the first member access of the binding.

## Workaround (in tree)

Use `match`, which gates correctly:

```
match hit_test_anchor(layout, dom, x, y):
    Some(anchor):
        return be_dom_get_attr(anchor, "href")
    _:
        return ""
```

Applied in `simple_browser_anchor_href_at` and
`simple_browser_first_anchor_center` in
`src/lib/gc_async_mut/web/simple_browser_page.spl`.

## Notes

- Same-file `Option` uses with `found.?` checks (e.g. `be_dom_find_by_id`)
  behave; only the `if val <name> = <call>:` binding form misfires.
- Verified via `bin/simple run` (JIT fell back to interpreter for the module).

## Resolution

Plain `if val`/`while val` desugars now mark their synthetic binding for
Option-only normalization. The interpreter returns nil for `Option::None` and
the payload for `Option::Some`; Result wrappers and ordinary empty values retain
their prior behavior, while explicit `.?` keeps its broader presence semantics.
Mirrored interpreter regression specs cover both if-expression and statement
forms, the None while-binding case, Result, and empty-value controls.
