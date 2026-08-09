# Tree-walk interpreter silently drops BOTH branches of an if/else whose bodies only `push`

**Date:** 2026-08-09
**Status:** OPEN
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
