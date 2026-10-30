# Seed: `alias Trait = field` forwarding unsupported

- **Severity:** P1
- **Status:** fixed (this change)
- **Component:** `src/compiler_rust/parser/src/types_def/mod.rs`, `parser_impl/core.rs`
- **Spec:** `test/01_unit/language/accessor_forwarding/accessor_forwarding_spec.spl`

## Symptom

```simple
class Host with Greeter:
    inner: English
    alias Greeter = inner
```

Interpreter: `error: semantic: variable `inner` not found`. JIT:
`GlobalLoad: unresolved identifier 'inner'`, then the same interpreter error.

## Root cause

The feature lives only in the pure-Simple source-to-source pass
`src/app/desugar/forwarding.spl` (Phase 3). The Rust seed never runs that pass,
and its class-body parser had no `alias` arm, so the line fell to
`parse_field` and became a bogus field whose default expression `inner` was
evaluated in the constructor.

## Fix

The class-body parser records `alias Upper = field` (uppercase name, `=`; the
`alias fn` / lowercase blanket forms are untouched). After the module parse,
`expand_trait_alias_forwards` clones each **abstract** trait method into the
class with body `self.field.m(params)` (types and `me` preserved). Because it is
plain AST, interpreter and HIR/JIT both see it. A method the class defines
explicitly is not forwarded (explicit wins). Unknown trait or non-field target
is a parse error rather than a silent no-op.

Green on both engines: `forwarded=hello, world`, `explicit_wins=HEY world`.

## Remaining gap (desugar parity)

`src/app/desugar/forwarding.spl` emits forwarders for every abstract method
without checking for an explicit definition in the class, so `LoudHost`
(explicit `greet` + alias) gets a duplicate `greet` from the desugar pass. The
seed now skips it; the desugar pass should do the same.

## Known limits (review follow-ups)

- The trait must be defined in the same module. An imported trait is a parse error, while the desugar pass silently forwards nothing.
- `alias` inside a nested (non-top-level) class or inside a mixin body is a parse error, not a silent drop.
- An explicit `self` parameter on the trait method is not passed as an argument (`self.inner.tag(n)`).
