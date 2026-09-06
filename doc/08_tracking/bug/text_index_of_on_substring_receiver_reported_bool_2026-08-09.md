# `text.index_of` on a substring receiver reported as returning a bool

## Status

**Reported, NOT REPRODUCED on the binary available at the time of writing.**
Do not treat this as a confirmed compiler defect yet, and do not cite it as the
cause of anything. It is recorded because the original observation was specific
and numeric rather than vague, and because the binary that observed it and the
binary that failed to reproduce it are **not the same build** — see
"Why the two runs may disagree" below. Reproducing it on a genuine pure-Simple
self-hosted binary would promote this to Open; a clean sweep there would retract
it.

## Original observation

While probing the SimpleOS WM `props=0` CSS custom-property chain, a host-side
probe reported that `index_of` on a temporary/substring receiver
data-dependently returned a **boolean** that coerces to `1`:

```
body = "\n  --radius-sm: 8px;\n"
body.index_of(":")                          -> 14    (correct)
body.substring(3, body.len()).index_of(":") -> true  (a BOOL; should be 11)
same shape on "--ui-bg: #0e0e10;"           -> 7     (correct)
```

The reason this would matter rather than merely being wrong: a bool coerces to
`1`, and `1 > 0`, so a `colon > 0` guard **passes** and the subsequent
`substring(0, colon)` / `substring(colon + 1, ...)` split silently produces
garbage names and values instead of failing loudly.

## Reproducer

```simple
fn main():
    val body = "\n  --radius-sm: 8px;\n"
    print "1 named            = {body.index_of(\":\")}"
    print "2 sub-temp         = {body.substring(3, body.len()).index_of(\":\")}"
    print "3 trim-temp        = {body.trim().index_of(\":\")}"
    print "4 sub-trim-temp    = {body.substring(3, body.len()).trim().index_of(\":\")}"
    val line = body.substring(3, body.len()).trim()
    print "5 named-line       = {line.index_of(\":\")}"
    if body.substring(3, body.len()).index_of(":") > 0:
        print "6 guard            = taken"
    else:
        print "6 guard            = NOT taken"
    val c7: i64 = body.substring(3, body.len()).index_of(":")
    print "7 typed i64        = {c7}"
    val other = "--ui-bg: #0e0e10;"
    print "8 other named      = {other.index_of(\":\")}"
    print "9 other sub-temp   = {other.substring(2, other.len()).index_of(\":\")}"
```

Run with:

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <file>.spl
```

## Negative result (2026-08-09)

Every shape returned the correct integer. The temporary receiver, the chained
`.trim()`, the guard position, and the explicitly-typed `i64` binding all agree
with the named-local baseline:

```
len=21
1 named            = 14
2 sub-temp         = 11
3 trim-temp        = 11
4 sub-trim-temp    = 11
5 named-line       = 11
6 guard            = taken
7 typed i64        = 11
8 other named      = 7
9 other sub-temp   = 5
```

No boolean, no coercion, no data dependence observed across two different
strings and nine receiver shapes.

## Why the two runs may disagree

The binary used for the negative sweep is **a Rust bootstrap seed sitting at the
pure-Simple deploy path**, not a self-hosted build:

- `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
- md5 prefix `e6b5d524caf5b6ee`, 29,573,408 bytes, dated 2026-08-08 12:14
- it prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`

Per `.claude/rules/bootstrap.md` the seed and the pure-Simple compiler are
**separate implementations** and routinely diverge on exactly this kind of
value-marshalling question. A boolean appearing where an `i64` index belongs is
the signature of a return-value marshalling or overload-dispatch fault, and the
seed and the self-hosted binary do not share that code. So a negative on the
seed is **not** evidence of absence on the pure-Simple binary.

Before this can be retracted, the sweep above must be re-run on a genuine
pure-Simple self-hosted `simple` and come back clean there too.

## Relationship to the WM `props=0` investigation — lead STRENGTHENED

`CssVarResolutionState.new` at
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:62`
calls `line.index_of(":")`. The stage-1/2/3 receipts added alongside this doc
ran in the SimpleOS WM lane on 2026-08-09 and localised the guest defect to
**exactly that statement's guard**:

```
[web-style-producer] css-props-stage3 props_len=1365 names_cap=200 guard=45 prop_count=0
[web-style-producer] css-var-unresolved count=49 first=--border-width-hairline idx=-1 props=0 sw_raw=1 sw_portable=1 css_len=4748
```

`css-props-stage1` and `css-props-stage2` were **silent**, so collection and
join both delivered the data intact — `props_len=1365` is byte-for-byte the
value the host produces. The loop ran its full `guard=45` iterations (45 lines,
one per property, matching the host's 45). Yet `prop_count=0`, and `prop_count`
increments **only** inside `if colon > 0`. Therefore `colon <= 0` on all 45
lines in the guest, while the host returns a correct index for the same input.

That is proven. What is **not** proven is which primitive breaks, because
`colon` depends on three of them in sequence:

```simple
val line = props.substring(pos, line_end).trim()   # substring, then trim
val colon = line.index_of(":")                     # then index_of
```

- `substring` returning empty → `colon = -1`
- `trim` returning empty → `colon = -1`
- `index_of` broken → `colon = -1` with a non-empty `line`

All three produce the observed receipt. A discriminating probe was added
(`raw_len` / `line_len` / `colon_index_of` / `colon_find_from` on the first
iteration) which separates them — a non-empty `line_len` with `colon_index_of<0`
while `colon_find_from` returns a real index would convict `index_of` outright.
**That probe has not yet been run in the guest** (the lane aborted on the
`wm-simple-web-build-source-changed` gate before boot), so no conclusion about
`index_of` may be drawn from the WM lane yet.

Note the two remaining arguments *against* `index_of`, unchanged:

1. `line` there is a **named local**, which is the one shape the original
   observation reported as *correct*.
2. The rest of that code path uses `find_from`, not `index_of`.

## Next step

Re-run the reproducer on a self-hosted pure-Simple binary produced by
`bin/simple build bootstrap`, and either promote this to Open with that
transcript or retract it.
