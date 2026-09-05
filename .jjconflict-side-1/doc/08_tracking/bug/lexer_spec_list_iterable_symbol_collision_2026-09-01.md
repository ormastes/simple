# `compiler/lexer_spec.spl`: co-compiled `List` symbol collision breaks `Iterable` trait check

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/compiler/lexer_spec.spl`, 0/1 examples executed;
  runner's own verdict reports `declared>=128`).

## Symptom

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/compiler/lexer_spec.spl
```

```
warning: public function `token_kinds` has 2 co-compiled definitions with 2
differing signatures ((text)->Generic { name: "List", args: [text] } vs
(text)->[TokenKind]); ... [compiler_cross_module_private_symbol_collision]
warning: method `List.from_iter` is defined by 2 separate co-compiled impl
blocks with 2 differing signatures ((I)->Generic { name: "List", args: [T] }
vs (I)->Self); ... [compiler_cross_module_method_collision]
warning: method `List.into_iter` is defined by 2 separate co-compiled impl
blocks with 2 differing signatures ((?)->Self.IntoIter vs (?)->Self.Iter);
... [compiler_cross_module_method_collision]

error: semantic: type `List` does not implement required method `iter` from
  trait `Iterable`
error: test-runner: no examples executed
```

The whole spec file (128 declared examples) fails to compile because
`compiler.lexer.*` / `compiler.lexer_types.*` pull in a `List` type whose
`from_iter`/`into_iter` are defined twice, by two different co-compiled impl
blocks with incompatible signatures. The compiler's own collision warning
already documents that "a call may silently dispatch to the wrong body" —
the semantic checker then concludes `List` doesn't implement `Iterable.iter`
at all (presumably because it picked the wrong/ambiguous
`from_iter`/`into_iter` pairing when resolving the trait requirement).

## Why not fixed here

This is a cross-module symbol/method-registry collision inside the
compiler's own type/trait resolution (`List` colliding between at least two
modules imported transitively by `compiler.lexer` / `compiler.lexer_types`),
not a bug in the spec file itself or in stdlib product code owned by
`test/01_unit/lib/std`. Diagnosing which two modules define conflicting
`List`/`token_kinds` symbols and de-duplicating them safely needs broader
compiler-internals investigation than a mechanical stdlib-test triage pass
should attempt.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/compiler/lexer_spec.spl 2>&1 | grep -E "warning:|error:"
```
