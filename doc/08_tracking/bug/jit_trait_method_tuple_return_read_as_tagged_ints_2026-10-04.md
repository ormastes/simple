# Seed JIT: `val (w, h) = host.size()` through a trait-bound receiver reads tagged ints (×8)

- **Filed:** 2026-10-04
- **Area:** Rust seed HIR/MIR typing of method calls on trait-bound (generic / trait-object) receivers
- **Status:** OPEN
- **Severity:** high — silent ×8 values; every `showcase_run(host: ScreenHost, ...)` frame is laid out at 8x the real size under JIT

## Repro

```simple
trait SizedHost:
    me size() -> (i32, i32)

class Box2:
    var w: i32
    var h: i32

impl SizedHost for Box2:
    me size() -> (i32, i32):
        (self.w, self.h)

fn area_of<H: SizedHost>(host: H) -> i64:
    val (w, h) = host.size()
    w.to_i64() * 1000000 + h.to_i64()

fn direct(b: Box2) -> i64:
    val (w, h) = b.size()
    w.to_i64() * 1000000 + h.to_i64()

fn main():
    val b = Box2(w: 1280, h: 720)
    print "generic={area_of(b)} direct={direct(b)}"
```

JIT (`SIMPLE_JIT_STRICT=1`, seed from origin/main f0b730f458b): `generic=10240005760 direct=1280000720`.
1280 → 10240 and 720 → 5760: the RuntimeValue integer tag (`<< 3`) is read as the value.

## MIR difference

`direct` (correct): `MethodCallStatic Box2.size` → stored as the tuple type →
`rt_tuple_get` → `UnboxInt` → `UnitNarrow 64→32` → `i32.to_i64`.

`area_of` (wrong): `MethodCallVirtual ... return_type: TypeId(17)` (the tuple), but
the result is **stored as TypeId(5)** (i64), the destructure goes through
`rt_index_get` with **Any** elements, and `w.to_i64()` becomes an untyped
`MethodCallStatic "to_i64"` on the still-tagged value. The HIR type of
`host.size()` on a trait-bound receiver is not the trait method's declared
return type.

## Damage observed

`src/app/ui_showcase/showcase_core.spl:677` (`val (w, h) = host.size()` with
`host: ScreenHost`) feeds 10240x5760 into `showcase_scene` for a 1280x720
surface under JIT, so `main_2d.spl` renders only the menu's first label and the
left panel; the group clip is `5118x1892` and the right panel lands at
`dx=5120`, off-surface. Interpreted runs are correct, so this was invisible on
macOS until large modules stopped panicking into the interpreter (see
`jit_macos_arm64_code_arena_linux_only_large_runs_interpreted_2026-10-04.md`).

## Related, found on the way

`"x".to_int() ?? 7` (an unparsable string): the JIT returns `0` and the
interpreter returns `120` (the char code of `x`). The expected value is `7`.
Not investigated further here.
