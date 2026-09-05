# `@unsafe` is rejected on class methods

## Status

Open compiler/language-surface bug found while hardening `FastTable` SFFI.

## Reproduction

```simple
class ForeignHandle:
    @unsafe(reason: "manual foreign lifetime", capabilities: [ffi])
    fn destroy():
        pass
```

The production check path reports `unexpected token in class body` at `@`.
The same attribute is accepted on module-level functions and raw extern
declarations.

## Impact

A class facade cannot express distinct unsafe obligations per method. The
fast-database compatibility facade therefore carries one class-level unsafe
contract and keeps every raw call inside lexical `unsafe(ffi)`. This is less
precise than marking only destruction and ambiguous legacy operations.

On 2026-08-27 this known grammar gap regressed the staged bootstrap when seven
method decorators were added to `PlatformEvent`: the already-admitted Stage-2
compiler rejected each decorator while parsing Stage 3. The compatibility fix
uses the same proven shape as `FastTable`: one module-level class contract plus
lexical `unsafe(capabilities: [ffi, raw_ptr])` scopes around the seven raw-call
dispatches. Raw extern declarations retain their individual contracts. The
compiler/language-surface bug remains open; production source must not require
a newer method-decorator grammar than the compiler it is bootstrapping from.

## Required fix

Parse declaration attributes before class `fn`, `me fn`, and `static fn`
members, preserve them in HIR, and enforce their capabilities at method call
sites identically to module-level functions. Add parser, HIR, safety-checker,
and call-site negative coverage before migrating the class-level annotation.
