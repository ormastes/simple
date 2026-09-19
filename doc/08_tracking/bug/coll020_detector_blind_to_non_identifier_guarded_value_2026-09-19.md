# COLL002/COLL020 are blind to a dedup guard whose value is not a bare identifier

**Status:** OPEN 2026-09-19
**Area:** `src/compiler/35.semantics/lint/collection_patterns.spl`
  (`is_manual_distinct_guard`, `push_stmt_array_name`, `is_contains_call`)
**Found by:** measuring Certain-fix coverage over the tree's real dedup sites
  for `doc/08_tracking/bug/coll_certain_fix_textual_proofs_disagree_with_parser_2026-09-19.md`

## What happens

Neither rule fires when the guarded value is anything other than a bare
identifier. Measured with the real CLI, one file, two functions:

```
fn get_unique_externals(deps: [Dep]) -> [text]:
    val seen: [text] = []
    for dep in deps:
        if not seen.contains(dep.path):      # <- field access
            seen.push(dep.path)
    return seen

fn plain(deps: [text]) -> [text]:
    val seen: [text] = []
    for d in deps:
        if not seen.contains(d):             # <- bare identifier
            seen.push(d)
    return seen
```

```
$ bin/simple lint probe/p1.spl
p1.spl:14:9: warning[COLL020]: manual dedup loop ... is O(n^2) ...
  fix: available [COLL020] (certain)
Found 0 error(s), 1 warning(s), 1 auto-fix(es) available
```

Line 14 is `plain`. `get_unique_externals` gets **no diagnostic at all** — not
COLL020, and not even COLL002, although `.contains()` on an array inside a
loop is exactly what COLL002 is for. The first function is the real one, from
`src/compiler/90.tools/depgraph/analyzer.spl:218`; the second is a reduction
of it. They are the same O(n^2) idiom with the same fix.

## Why it matters

This is the dominant ceiling on the feature, and it is a DETECTION gap, not a
safety refusal. Over the 68 real dedup sites in 52 files:

- **26 of 68 (38%)** guard on something that is not a bare identifier —
  `dep.path`, `f(x)`, `xs[i]`, a concatenation. Every one is silently
  un-warned, so the Certain door never gets a chance to prove anything.
- 10 of 68 have a guard body with more than one statement, which
  `manual_distinct_guard_body_pushes` also rejects (it requires every
  statement in the body to be a push of the guarded value).

Those two account for most of the gap between 68 sites and the 8 that get a
Certain fix. The remaining refusals are the Certain door doing its job:
parameters, reassignment of the array, `.sort()` on it, and same-receiver
multi-site loops.

## What the fix would need

`is_manual_distinct_guard` compares the guarded value and the pushed value by
NAME. It should compare them structurally — the same expression subtree in the
`contains` argument and in the `push` argument — which the arena can answer
without any new accessor. The generated Dict key is then that expression,
emitted once into a local:

```
var seen_set: Dict<text, bool> = {}
...
    val _k = dep.path
    if not seen_set.contains_key(_k):
        seen_set[_k] = true
        seen.push(_k)
```

That is a bigger rewrite than the current one (it introduces a binding, so it
needs the same name-freshness proof the Dict name already gets), and the
expression must be proven side-effect-free before it can be evaluated once
instead of twice — `f(x)` is not. Both are checks the Certain door already
knows how to express; neither is in place.

## Deliberate scope note

Not attempted in the round that found it. The Certain door had just closed 21
measured wrong rewrites across four rounds, and widening WHAT IT SEES is a
separate change class from proving what it may rewrite. A correct warning with
no fix is a fine outcome; a wrong rewrite is not.

## A second, related blindness in the same family

`if not allowed.contains(x):` — the plain FILTER form, with no push onto
`allowed` — also produces no COLL002. Verified with the real CLI on a
two-array fixture: `Lint passed: all files clean`. The cause is visible in the
source: the if-condition path tests `is_contains_call(cond)`, and under `not`
the condition node is a unary expression, not the method call. The positive
form `if arr.contains(t):` is detected (two sites, `amb.spl:6:12` and `8:12`,
each carrying its own Certain fix), so this is specifically the negated one.

Both blindnesses live in the same place — the rule asks whether ONE node has
the shape it expects, instead of looking for the `contains` call anywhere in
the condition — and a fix for one should cover the other.

## Two precision notes on the measurement above

- The "26 of 68" figure is a **classification by argument text** over the site
  list, not 26 separate CLI runs. Two were confirmed against the real CLI: the
  original `src/compiler/90.tools/depgraph/analyzer.spl` (6 warnings, none
  COLL) and its two-function reduction.
- **Why COLL002 is also silent on the field-access form is not established
  here.** COLL002 has its own `.contains()`-in-loop path that does not depend
  on the push, so a handoff or suppression between the two rules is the
  likely cause, but it was not traced. Whoever fixes COLL020's matcher must
  re-check that interaction rather than assume one change covers both.

## The trap a fixer will hit first

Do not fix the negated-filter blindness by simply looking for a `contains`
call anywhere in the condition. **Every COLL020 site is a negated filter** —
`if not X.contains(v): X.push(v)` is the dedup idiom itself — so a naive
widening makes COLL002 fire on all of them and every dedup site reports
twice, once as O(n^2)-per-iteration and once as a manual dedup loop. A fix
must exclude the guards COLL020 already claims.
