# Tree-walk interpreter silently drops BOTH branches of an if/else whose bodies only `push`

## 2026-09-13 — a likely explanation for the original sighting (entry stays CLOSED)

Stays CLOSED — this adds a candidate cause for the "either the defect was
specific to the since-replaced binary, or C8's probe mismeasured" dangling end
below, so a future recurrence is not re-investigated from zero.

There is a live defect that produces **exactly** this symptom and is invisible
to the 20-shape sweep recorded below: at **module scope** (top-level statements,
outside any `fn`), the seed executes statements against a discarded copy of the
scope, so mutations performed inside a loop or branch body vanish while the
body demonstrably runs. Measured 2026-09-13 on
`build/vt4/bootstrap/simple.exe`, and tracked at
`top_level_array_index_assign_in_loop_silently_dropped_2026-08-25.md`
(re-characterised the same day: it is not limited to array-index writes, a plain
`n = n + 1` is dropped too, and it is sensitive to how many top-level
declarations precede the construct — a reduced repro can flip it clean).

Why this fits the original report and evades the sweep:

- it presents as "the body ran but nothing was pushed", with exit 0 and no
  diagnostic — the reported shape;
- every shape in the table below was almost certainly probed **inside a
  function**, where the defect does not occur, so all 20 correctly came back OK;
- it is position-sensitive, which explains a sighting that would not
  re-reproduce on a re-run of a slightly different program.

Independently corroborated the same day: the `MirToWat`/`WatBuilder` probe in
`chained_static_ctor_receiver_drops_mutation_2026-08-01.md` prints `[]` for all
three receiver forms at module scope and the correct `[i64.const 7]` for all
three inside `fn main()` — the same push-only-body-drops-silently signature,
from the same cause.

**Action if this ever recurs:** before reopening, check whether the failing
probe was module-scope. The regression spec
`test/01_unit/bugs/if_else_push_only_branch_spec.spl` runs inside a spec block
and so cannot catch the module-scope variant.


**Date:** 2026-08-09
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## 2026-08-09 follow-up: cannot reproduce on any engine

Investigated on the shared WC (binary: Rust seed at
`bin/release/x86_64-unknown-linux-gnu/simple`). ~20 shapes probed, including a
faithful reconstruction of the original `cache_explain` site (struct-field
condition `lookup.hit`, push of concatenated field accesses, one and two
pushes per arm, long surrounding push sequence):

| Shape | interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) | spec harness (`bin/simple test`) | JIT (`bin/simple run`) | native (`native-build`) |
|---|---|---|---|---|
| if/else single push, literal cond | OK (len=1) | OK | OK | OK |
| if/else single push, comparison / struct-field cond | OK | OK | OK | — |
| elif chain, single push per arm | OK | OK | OK | — |
| while / match arms / nested if, push-only | OK | — | OK | — |
| `.set` / `.insert` / nested `ll[0].push` only bodies | OK | — | `.set` fails with known dict-set dispatch gap (separate bug) | — |
| two pushes per arm (original t10 shape) | OK | — | OK | — |

No shape drops a branch. Either the defect was specific to the (since
replaced) binary/state C8 ran under, or C8's probe mismeasured (the missing
tier line had another cause). Regression spec guarding the shape:
`test/01_unit/bugs/if_else_push_only_branch_spec.spl` (4/4 green;
sabotage-verified — neutralizing the pushes turns it RED).

Blast radius if it ever recurs: 187 if/push/else/push sites across 160
`*_spec.spl` files (`/usr/bin/grep`-based sweep, 2026-08-09).
**Severity:** silent wrong output under the interpreter; JIT is correct — so this is engine divergence, not a uniform bug
**Found by:** agent C8 while building `cache_explain.spl`

## Symptom

An `if/else` whose branch bodies consist ONLY of a `push` to a list executes
**neither** branch under the tree-walk interpreter. No error, no diagnostic —
the list simply does not receive the element.

The same code is CORRECT under the JIT.

Observed:

- `bin/simple run` (JIT) — probe printed all four assertions true.
- `bin/simple test` (tree-walk interpreter) — rendered **neither** tier line.

## Why this matters far beyond the one call site

`bin/simple test` hard-defaults to the tree-walk interpreter. This campaign
verified nine stages — roughly 180 spec examples — entirely under that engine.
Any of them containing this pattern could be passing or failing for reasons
unrelated to the logic under test.

It also means the usual reasoning is inverted: normally a green under a slower,
simpler engine is the conservative result. Here the interpreter is the WRONG
one and the JIT is right, so interpreter-green is not the safe side.

## Workaround applied in `cache_explain.spl`

Restructure so the branches compute into locals and the `push` happens
unconditionally outside the conditional:

```
# BROKEN under interpreter — both branches dropped
if cond:
    lines.push(a)
else:
    lines.push(b)

# WORKS
val line = if cond: a else: b
lines.push(line)
```

## What is NOT yet known

- The precise trigger boundary. Is it *only* when the body is a single `push`?
  Does it apply to other mutating-method-only bodies (`.set`, `.append`,
  `.insert`)? Does an extra statement in the branch mask it?
- Whether `while`/`match` arms with the same shape are affected.
- Whether native codegen agrees with the JIT or the interpreter.

Answering the trigger boundary is the first task for whoever picks this up —
it determines how much existing spec evidence is suspect.

## Suggested next step

1. Minimal reproducer: a spec that pushes in both arms and asserts list length.
   Run it under `bin/simple test` (interpreter), `bin/simple run` (JIT), and a
   native build. Record all three.
2. Sweep the spec corpus for the pattern (`/usr/bin/grep`, NOT the wrapped
   ugrep which undercounts) to size the blast radius.
3. Fix in the interpreter's statement evaluation.

## Related

- `.claude/rules/testing.md` — `bin/simple test` never reaches the JIT.
- `doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md`
  — compounding factor: the binary running all of this is the Rust seed.
