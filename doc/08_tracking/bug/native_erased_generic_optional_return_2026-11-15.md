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

## Same family: bool payload in a generic method's `Result`

```
class G<T>:
    n: i64
impl G<T>:
    me set(value: T) -> Result<bool, text>:
        Ok(true)
var g: G<i64> = G(n: 0)
match g.set(5):
    case Ok(b): print "set {b}"     # expect "set true"; native prints "set 1"
```

Pre-fix Stage 2, cranelift: `set 1`.

## Observed on the real module (Stage 2 `81625788a20`, cranelift)

A probe imports `attribute_schema_v1` and drives `AttributeStoreV1<i64>` with a
local `impl AttrOwnerV1<i64>`, in direct, column and detached-embedded
placements: has/get/set/retire/len, a None read, and a write-then-read.

- The output matches the seed on every line, including `9000000000` through
  the owner, except `set` printing `1` for `Ok(true)` (the issue above).
- The `-> T?` miscompile does not show up there. The module never returns `T?`
  from a generic method to a concrete caller; reads go through
  `owner_read` (trait dispatch) or `Result<T, text>`.
- **llvm:** the build fails in codegen for `sha256`, `sdn.parser`,
  `data_schema_resolver` and `data_schema_core_v1` (llc error: `'%lN' defined
  with type 'i64' but expected 'ptr'`). The same llc failure in `sha256` and
  `sdn.parser` reproduces on the pre-fix Stage 2 with a trivial importer.
