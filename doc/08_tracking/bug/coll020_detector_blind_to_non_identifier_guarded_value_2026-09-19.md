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
