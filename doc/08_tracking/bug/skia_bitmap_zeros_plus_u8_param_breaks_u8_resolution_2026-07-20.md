# `Bitmap.zeros(...)` call + a `u8`-typed function param in the same file breaks all `u8` resolution

- **Status:** OPEN
- **Discovered:** 2026-07-20, whole-suite triage campaign
- **Area:** compiler semantic analysis — primitive-type symbol resolution,
  interaction between `std.skia.backend.cpu.raster_prims.Bitmap` static
  constructor and locally-declared functions with a `u8` parameter
- **Severity:** Medium — breaks a whole class of skia-adjacent code that
  mixes `Bitmap` construction with `u8` alpha/byte parameters; reproduces
  under BOTH `bin/simple run` and `bin/simple test` (not the usual
  test-vs-run evaluator divergence — this is a real shared-path bug).

## Symptom

`test/unit/lib/skia/mask_filter_spec.spl` fails all 4 `apply_mask_filter`
examples (Identity/Blur/Emboss/Shadow) with:

```
semantic: variable `u8` not found
```

## Minimal repro (fully isolated — no invocation even required)

```spl
use std.skia.backend.cpu.raster_prims.{Bitmap}

fn _set_alpha(bmp: Bitmap, a: u8):
    print(2)

fn other(bmp: Bitmap):
    print(bmp.width)

fn main():
    val out = Bitmap.zeros(4, 4)
    other(out)

main()
```

Run: `bin/release/x86_64-unknown-linux-gnu/simple run <this file>` →
`error: semantic: variable \`u8\` not found`. Note `_set_alpha` is never
called — merely **declared** in the same file as a `Bitmap.zeros(...)` call
site is sufficient to break `u8` resolution elsewhere in the file.

## Isolation notes (bisected this session)

- Declaring `_set_alpha(bmp: Bitmap, a: u8)` in a file with **no**
  `Bitmap.zeros(...)` call anywhere: compiles and runs fine (prints `hi`).
- Calling `_set_alpha(bmp: i64, a: u8)` (non-`Bitmap` first param) with an
  actual `255 as u8` argument: works fine, prints `1`.
- Calling `_set_alpha(a: u8)` (`Bitmap` import present but not used as a
  param type) with `255 as u8`: works fine, prints `1`.
- The failure requires ALL of: (1) `std.skia.backend.cpu.raster_prims.Bitmap`
  imported, (2) some function in the file typed `(bmp: Bitmap, ...)` with
  a `u8`-typed parameter alongside it, AND (3) `Bitmap.zeros(...)` actually
  called somewhere in the file (even in an unrelated function). The `u8`
  parameter's OWN function does not need to be called.

This strongly suggests `Bitmap.zeros`'s static-constructor type
inference/monomorphization interacts with the module's primitive-type symbol
table (`u8`) and corrupts/shadows it when a `Bitmap`-typed parameter
co-occurs with a `u8`-typed parameter in the same declaration — consistent
with the "private helper has N co-compiled definitions with differing
signatures" cross-module symbol-collision class already seen in other
`compiler_cross_module_private_symbol_collision` warnings this session, but
this specific `u8`-vanishes-as-a-type manifestation does not yet have a
dedicated doc.

## Failing command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/skia/mask_filter_spec.spl --no-session-daemon
```

## Note

Not a stale test — `test/unit/lib/skia/mask_filter_spec.spl`'s helper
functions (`_set_alpha`, `_make_disk`) and the `255 as u8` casts are
syntactically and semantically correct Simple; the failure is a genuine
compiler defect triggered by this specific type combination, reproduced
independently outside the test harness via plain `bin/simple run`. Not
attempted here — root-causing requires reading the compiler's semantic
analysis / symbol-table source, out of scope for a spec-only triage pass.
