# Units

The unit system gives Simple programs first-class typed measurement values.
A `km` is not an `f64` — it is a distinct unit type that carries dimension
and scale metadata. The compiler prevents accidental mixing (`km + kg`
is a compile error) and the standard catalog ships with every
human-measurement domain pre-populated.

- Feature:  `unit-system-consolidation`
- State:    `.sstack/unit-system-consolidation/state.md`
- Spec:     `test/unit/lib/unit/unit_*.spl`

## 1. Directory Layout

All units live under `src/unit/`. The default organisation is
`simple-lang` and is resolved from either `src/unit/simple-lang/` or
the `.com`-suffixed alias `src/unit/simple-lang.com/` — both paths point
at the same physical tree.

```
src/unit/
  simple-lang/
    length/        # km, m, cm, mm, mi, ft, in, ly, pc, ...
    mass/          # kg, g, mg, lb, oz, t, ...
    time/          # s, ms, us, ns, min, h, day, ...
    temperature/   # K, C, F, R
    electric/      # A, V, W, Ohm, ...
    amount/        # mol
    luminous/      # cd, lm, lx
    angle/         # rad, deg, grad, turn, ...
    area/          # m2, km2, ha, acre, ...
    volume/        # L, mL, gal, m3, ...
    velocity/      # mps, kmph, mph, knot, fps, mach, c
    acceleration/  # m_per_s2, g_force, ...
    force/         # N, lbf, ...
    energy/        # J, kJ, Wh, kWh, cal, BTU, eV, ...
    power/         # W, hp, ...
    pressure/      # Pa, bar, atm, psi, Torr, mmHg, ...
    frequency/     # Hz, kHz, MHz, BPM, RPM, ...
    data/          # bit, byte, KB, MB, GB, TB, KiB, ...
    currency/      # USD, EUR, JPY, ... (ISO 4217)
    calendar/      # year, month, week, day_cal, ...
    geo/           # lat, lon, heading, ...
    graphics/      # px, pt, em, rem, ...
    ui/            # dp, sp, percent_ui, ...
    net/           # bps, Kbps, Mbps, Gbps, ...
    astronomy/     # AU, parsec, ly, jansky, ...
    chemistry/     # molar, ppm, pH, ...
    culinary/      # tsp, tbsp, cup, ...
    regional/      # li (Chinese), ri (Korean), ...
    typography/    # cpi, lpi, ...
    composite/     # kmph, mps, Nm, Wh, kg_per_m3, m_per_s2, ...
    meta/
    __init__.spl
  <org>.com/       # third-party domains (see §4)
```

Rule of thumb: pick the **subject folder** for atomic units and the
**`composite/`** folder for derived units that arise from division or
multiplication of atomic units.

## 2. Postfix Literal Syntax

Append `_<symbol>` directly to a numeric literal to tag it with a unit
type. The lexer rule: `_` followed by an **alphabetic** character starts
a unit suffix; `_` followed by a **digit** is a plain digit separator.

```simple
val distance   = 10_km         # length — km
val speed_lim  = 60_kmph       # composite velocity
val width      = 0_x           # layout — x-axis
val weight     = 1_w           # layout — weight
val separator  = 10_000_km     # separator + suffix — 10000 km
val energy     = 2.5_Wh        # float + composite
```

Typed-literal forms that already worked (`10_i64`, `3.14_f32`,
`10_u8`) continue to lex as before. A `_<symbol>` that is not a
registered numeric or unit suffix is an error with a suggestion from
the closest registered unit.

## 3. Import Forms

Two equivalent import paths resolve to the same module. Pick the shorter
form unless you need to disambiguate between organisations:

```simple
# short form (default org)
use unit.length.{km, m}
use unit.velocity.{kmph}

# canonical form — identical result
use unit.simple-lang.length.{km, m}
use unit.simple-lang.velocity.{kmph}
```

The `unit.` prefix joins `std.`, `lib.`, `app.`, `compiler.` as a
well-known resolver root. The self-hosted module loader
(`src/compiler/10.frontend/core/interpreter/module_loader.spl`) and the
Rust seed (`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`)
both recognise it.

## 4. Third-Party Organisations

Other organisations register units under `src/unit/<org>.com/`. The
`.com` suffix is the on-disk marker; the import path omits it.

```simple
# src/unit/acme-corp.com/robotics/joint_angle.spl
use unit.acme-corp.robotics.{joint_angle}
```

If both `unit.<org>.<subject>` and `unit.simple-lang.<subject>` expose
the same symbol, an **explicit** `use unit.simple-lang.<subject>`
shadows the third-party import (canonical form wins).

## 5. Composite Units

Composite (derived) units live in `src/unit/simple-lang/composite/` and
are declared as ratios or products of atomic units:

```simple
# src/unit/simple-lang/composite/kmph.spl
class Kmph:
    value: f64

    fn to_f64() -> f64: self.value

    static fn kind() -> text: "Velocity"
    static fn symbol() -> text: "kmph"
    static fn numerator() -> [text]: ["km"]
    static fn denominator() -> [text]: ["h"]
    static fn scale_to_base() -> f64: 0.277777777777778  # to m/s

export Kmph
```

Arithmetic is dimension-aware:

```simple
val d = 100_km
val t = 2_h
val v: kmph = d / t       # => Kmph(value: 50.0)
expect(60_kmph).to_be_close_to(16.6667_mps, 1e-4)
expect(1_km + 1_kg)      # ❌ compile error: dimension mismatch
```

Authoring pattern for a new composite:

1. Decide the decomposition (`km / h`, `N * m`, `m ^ 2`).
2. Add a file under `composite/` with the ratio/product declaration.
3. Set `scale_to_base()` to map into the canonical SI unit.
4. Register any alias in the subject's `__init__.spl` re-exporter so the
   composite is reachable via `unit.<subject>.{Name}` as well as
   `unit.composite.{Name}`.

## 6. Raw-Primitive Warning

Passing a raw `i32`/`i64`/`f64` to a parameter declared with a unit
type emits a **warning** (not an error) — migrations stay incremental.

```simple
fn move(d: km) -> text:
    "moved " + d.to_text()

move(10)           # ⚠ warning: raw primitive passed to unit-typed
                   #   parameter 'd: km'; use '_km' postfix or explicit
                   #   conversion.
move(10_km)        # ✓ ok
move(km(10.0))     # ✓ ok — explicit construction
```

Suppress locally with the attribute form:

```simple
#[allow(raw_unit)]
move(10)           # ✓ no warning
```

The lint only fires at the call site. Inside unit-typed code paths
(where the type flows from another unit variable) the warning is
suppressed automatically.

## 7. Migration from `std.common.units.*`

The old path `src/lib/common/units/` is now a deprecated shim that
re-exports from `unit.simple-lang.*`. Existing code compiles for one
release cycle and emits:

```
warning: 'std.common.units.*' is deprecated; moved to
'unit.simple-lang.*'. Removal planned in 0.11.0.
```

Old tree `src/lib/std/src/units.disabled/` has been removed entirely.
Update imports to the new paths at your convenience:

```simple
# before
use std.common.units.length.{km, m}

# after
use unit.length.{km, m}
```

## 8. Related Files

- Lexer: `src/compiler_rust/parser/src/lexer/numbers.rs`
- Rust-seed resolver: `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`
- Self-hosted resolver: `src/compiler/10.frontend/core/interpreter/module_loader.spl`
- HIR lowering: `src/compiler/20.hir/hir_lowering/expressions.spl`
- Raw-unit lint: `src/compiler/40.sema/lints/raw_unit.spl`
- Migration shim: `src/lib/common/units/__init__.spl`
- Catalog source: `doc/06_spec/world_units_v1.sdn`
