# Native primitive `to_i64` collides with imported custom methods

Status: open compiler blocker; three fix/review cycles exhausted on
2026-07-24. The rejected compiler series is `846e0912`, `d31b708e`,
`d5d91957` and is intentionally not integrated.

## Reproduction

The native Aetheric Web renderer archive contains three unresolved references
to:

```text
lib.nogc_sync_mut.failsafe.core.LogLevel.to_i64
```

The callers are scalar conversions in Engine2D `draw_ir_adv` and `glyph`.
Adding `src/lib/nogc_sync_mut/failsafe/core.spl` as an explicit native-build
source does not emit the method into the entry closure and does not change the
link failure. Current MIR lowering has no complete primitive `to_i64` owner
path, so generic method resolution can bind an unrelated imported method with
the same leaf name.

## Rejected repair

The three-cycle candidate added a primitive-first MIR cast and then repaired
receiver caching and inferred-text detection. High-capability review rejected
integration:

1. the primitive probe was not restricted by `MethodResolution`, so an
   integer-shaped enum or trait receiver with missing HIR type could bypass a
   resolved custom `to_i64` method and expose its storage value;
2. detecting inferred text only prevented the cast—it did not replace a stale
   imported resolution with the real text parse-to-`Option` owner; and
3. direct x86-64/AArch64 native selectors currently lower MIR `Cast` as a
   register move, so including `f32`/`f64` would not perform the numeric
   truncation provided by LLVM/Cranelift.

The shared prelowered receiver reuse was accepted: it prevents duplicate
evaluation in instance, trait, free-function, and unresolved dispatch. That
piece alone is insufficient to fix the collision.

## Required semantic regression

Replace the source-substring test with one native fixture that:

- imports the colliding `LogLevel.to_i64`;
- proves a side-effecting primitive receiver converts once;
- proves resolved enum instance and trait methods return sentinel values, not
  discriminants;
- proves inferred valid and invalid text return `Some(value)` and `None` and
  evaluate the receiver once;
- covers Bool, Char, unsigned high-bit values, and positive/negative
  fractional floats on every enabled native backend; and
- inspects the emitted object/archive to reject any `LogLevel.to_i64`
  reference from primitive Engine2D call sites.

The next implementation must first gate primitive recovery to the exact
resolution states it can safely override, then repair stale text resolution at
its owner. Floats must remain excluded until each selected backend performs a
real numeric conversion.

## Resume gate

After the focused native fixture passes, build an exact-current pure-Simple
Stage 3 compiler and run the remaining Aetheric producer cycle once:

```sh
SIMPLE_BIN=/absolute/path/to/exact-current-stage3-simple \
BUILD_DIR=build/aetheric-host-web-gui-current \
AETHERIC_HOST_WEB_GUI_PROOF=build/aetheric-host-web-gui-current/aetheric-host-web-gui.env \
sh scripts/check/produce-aetheric-host-web-gui-evidence.shs
```

Only if the producer completes may the admission wrapper run. Do not add a
`LogLevel` object manually, add a raw runtime alias, rename feature call sites,
or treat the existing partial artifacts as evidence.
