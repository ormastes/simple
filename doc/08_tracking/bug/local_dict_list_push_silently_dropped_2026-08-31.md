# Bare local dict-of-list `d[k].push(v)` silently drops the mutation (interpreter)

**Date:** 2026-08-31
**Status:** OPEN — reproduced incidentally, needs a minimal reduction + spec
**Severity:** high — silent data loss, no error, no diagnostic
**Found by:** graph fusion source work (`src/app/spipe/fusion/graph_source.spl`)

## Symptom

Under `bin/simple test`'s tree-walk interpreter, for a **bare local variable**
holding a `{text: [list]}` dict:

```
d[k].push(v)      # k already present -> mutation is SILENTLY DROPPED
```

The push appears to succeed. No error, no warning, no diagnostic. The value is
simply not there on the next read.

The **identical pattern through a class field persists correctly**:

```
self.m[k].push(v)   # works -- this is exactly ReverseIndexV1._insert's shape
```

## Why this is dangerous

This is not a compile error or a crash — it is a wrong answer. Any index,
adjacency map, postings list, or accumulator built on a bare local dict-of-list
is quietly incomplete, and every test over it passes while under-reporting.
Small fixtures can easily miss it: the drop only shows when a key is pushed to
more than once.

It is also easy to mistake for a COW-alias mistake (`val t = self.x; t.push(...)`,
see `.claude/rules/code-style.md`) and "fixed" by cargo-culting an owner class,
which is what happened here — the workaround is correct but the underlying
defect stays hidden. Class-field indirection is currently the only known-good
shape.

## Workaround in place

`graph_source.spl` wraps forward adjacency in a small owner class
`_ForwardIndex`, mirroring `ReverseIndexV1`, instead of using a bare local dict.
Documented in that file's header. **This is a workaround, not a fix** — recorded
here rather than normalized silently, per CLAUDE.md.

## Not yet established

- Minimal reduction (the observation is from real code, not a reduced case).
- Whether it also affects native codegen or only the tree-walk interpreter.
- Whether other container shapes are affected (`{text: dict}`, nested lists).
- Whether an existing bug record already covers this; check before fixing.
  Related but DISTINCT: the native-codegen Dict gaps in
  `doc/07_guide/language/dict_native_pitfalls.md` (that truth table is about
  `.get()`/bracket-read on native, not about a dropped `push` in the
  interpreter).

## Next step

Reduce to a minimal spec under `test/01_unit/compiler/`, confirm the
interpreter/native split, then fix. Until then, prefer an owner class over a
bare local dict-of-list anywhere correctness depends on the push landing.
