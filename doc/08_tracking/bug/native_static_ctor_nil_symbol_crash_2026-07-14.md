# native-build: struct/class with a `static fn new()` crashes (nil-symbol)

**Severity:** high (loud crash — blocks ALL stdlib collections)
**Found:** 2026-07-14, collections lane
**Backend:** native-build `--entry`

## Symptom

Any struct/class that defines a `static fn` constructor (e.g. `Type.new()`)
aborts native-build with:

```
undefined field 'id': cannot access field on value of type 'nil'
```

Minimal repro: a struct with a single `static fn new()` returning `Type(...)`.
Structs with only instance methods build+run fine (verified PASS). This blocks
`Set<T>`, `Map<K,V>`, `Stack`/`Queue`/`Deque`, `HashSet`/`HashMap`, `BTree*` —
every stdlib collection uses `Type.new()`/`with_capacity()`.

This is a **loud** failure (correct discipline — no binary emitted), but it is
the single largest gap blocking collection support on the native path.

## Root cause (suspected)

Nil-symbol handling in HIR→MIR static-call lowering — `lower_call` /
`NamedVar` resolution in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` and
`expr_dispatch.spl`. The static-method receiver (the type name) resolves to a
`nil` symbol, then field access on the constructed value dereferences it.

## Fix direction

Resolve a `Type.static_method()` callee to the type's associated function symbol
(not a value binding) before lowering the call; the constructor return value's
struct type must be threaded so subsequent `.field` access has a real type, not
`nil`.

## Reproduce

`/tmp/wt_collections/` probes (`map1.spl`, `hashset_min9.spl`).
