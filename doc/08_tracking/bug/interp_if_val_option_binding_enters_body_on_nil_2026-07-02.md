# Interpreter: `if val x = <Option-returning fn>:` enters the body when the result is nil

## Re-verified 2026-09-13 — seed lane clean; pure-Simple lane still unverified (LEFT OPEN)

**Lane caveat (added in the same 2026-09-13 pass, after review):** this entry is
filed against the **pure-Simple / self-hosted** lane, which the run recorded
below does NOT exercise. No self-hosted binary is deployed on this host —
`bin/release/simple.exe`, `bin/release/x86_64-pc-windows-msvc/simple.exe` and
`bin/release/x86_64-pc-windows-gnu/simple.exe` all print the Rust
bootstrap-seed banner. Running the repro through the pure-Simple CLI on the
seed (`simple run src/app/cli/main.spl -- run <repro>`) emitted only lint
diagnostics and never executed the program, so that substitute lane does not
work either. The seed result below therefore shows only that the **seed** does
not exhibit the defect; it does NOT discharge the pure-Simple fix.
**This entry stays OPEN pending a deployed self-hosted binary.**

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran an Option-returning function through `if val` on both the nil and the
Some path in one program:

```spl
fn get(f: bool) -> i64?:
    if f:
        return 5
    nil

fn main():
    if val x = get(false):
        print("BAD entered with {x}")
    else:
        print("OK nil skipped")
    if val y = get(true):
        print("OK some {y}")
    else:
        print("BAD skipped some")
```

Output:

```
OK nil skipped
OK some 5
```

The nil case no longer enters the match branch and the Some case still binds
the payload correctly. The "executable interpreter proof pending" caveat is
discharged on the seed lane (measured, not inferred).

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
