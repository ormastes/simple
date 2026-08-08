# native-build: struct/class with a `static fn new()` crashes (nil-symbol)

**Severity:** high (loud crash — blocks ALL stdlib collections)
**Found:** 2026-07-14, collections lane
**Resolved:** 2026-07-15
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

## Root cause

The production method-resolution pass uses an empty symbol table, so a
`Type.new()` call reaches MIR as `MethodResolution.Unresolved`. The unresolved
MIR branch then lowered the type name as an instance value and dereferenced the
result local, producing the nil-symbol crash. Static methods also appeared in
the free-function ambiguity scan and collided with their own bare name.

## Resolution

MIR module setup now records named-struct-returning static methods under a
static-only key. The unresolved call path recognizes a type receiver, emits only
the explicit arguments through the shared resolved-call helper, and restores
the declared struct result type before chained field access. Static methods are
excluded from the free-function scan. Same-module duplicate bare method names
fail the build explicitly instead of emitting a crash-prone binary. Each HIR
module also resets method SymbolIds, ambiguity flags, and return metadata before
entry-closure lowering switches to that module's symbol table.

## Regression evidence

`scripts/check/check-native-seed-parity.shs` includes:

- `static_ctor_field`: `Point.new().y` matches the seed oracle (`7`).
- `static_ctor_ambiguous_loud`: two bare `new` symbols fail with no binary.
- `mir_lowering_new_spec.spl`: all four method metadata maps are reset at the
  shared `MirLowering.lower_module` boundary.

The complete parity gate reports `total=38 pass=38 fail=0` and
`native_seed_parity=true`. This resolves the local named-struct constructor
layer; it does not claim every generic stdlib collection is now native-ready.
