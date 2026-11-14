# Native: erased generic class `T?` returns/params miscompile (2026-11-15)

**Status:** open. Pre-existing: reproduces on the pre-fix Stage 2
(`pinned-8220cfef5b8a/.../bootstrap-fable-33/.../stage2-admitted/simple`) and on
the Stage 2 built from `81625788a20`. Involves no traits.

## Repro (`native-build main.spl --entry-closure`, SIMPLE_BOOTSTRAP=1)

```
class Box<T>:
    v: T?
impl Box<T>:
    fn read() -> T?:
        self.v
    fn none_read() -> T?:
        None
    me put(value: T):
        self.v = Some(value)

fn show_i64(tag: text, v: i64?):
    match v:
        case Some(x): print "{tag} some {x}"
        case None: print "{tag} none"

fn main():
    var b: Box<i64> = Box(v: Some(41))
    show_i64("i read", b.read())        # expect: i read some 41
    show_i64("i none", b.none_read())   # expect: i none none
    var f: Box<f64> = Box(v: Some(1.5))
    f.put(2.5)                          # cranelift: verifier error here
main()
```

- **llvm:** `i read some 196953466405569`, and `i none some <handle>`. The
  concrete caller re-wraps the generic method's Option handle as
  `Some(handle)`, because bootstrap HIR erases the template's `-> T?` return to
  i64 and generic-impl methods publish no Function symbol type. f64 prints
  denormals, which is the same double wrap.
- **cranelift:** `arg 1 (v200) has type f64, expected i64`. A raw f64 is
  passed into the erased `T` parameter.

## Why a signature-only fix is wrong

Publishing the `-> T?` signature for generic-impl methods removes the re-wrap
and the f64 arg error. However, `Some(value: T)` built inside an erased body
then carries a *tagged* runtime word (`rt_value_int_wide` = `v<<3|tag`, f64
heap-boxed), while concrete `X?` readers decode the payload *raw*
(`enum_payload_value`). That turns a refusal into silent wrong values, so it
was reverted. A real fix must pick one payload representation at the erased ↔
concrete boundary: either convert at call/return, or monomorphize.

## Impact

`src/compiler/00.common/data/attribute_schema_v1.spl` `AttributeStoreV1<T>`
(`-> T?` methods, `slots: [T?]`, `Dict<i64, T>`) is affected natively,
independent of the `AttrOwnerV1<T>` trait-object fix (`f6fa77f4789`,
`81625788a20`). The trait part is verified on both backends by
`test/fixtures/native_generic_trait_object_optional_field/main.spl`, which uses
non-generic holders.
