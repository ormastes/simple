# Native: erased generic class `T?` returns/params miscompile (2026-11-15)

**Status:** open. Pre-existing and involves no traits. The `Box<T>` and
`G<T>` repros below were run on an older Stage 2 (run 33,
`/home/yoon/dev/simple-boot-fable-20261112/build/bootstrap/pinned-src/pinned-8220cfef5b8a/build/bootstrap-fable-33/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`)
and on the Stage 2 built from `81625788a20` (pre-rebase sha of `1570c5778b8`). The true pre-fix base is run 34
(`.../pinned-43d59a399477/build/bootstrap-fable-34/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`).
The reviewer reproduced the trait-free SparseHash ÷8 below on it.

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

## Observed on the real module (Stage 2 `81625788a20` = rebased `1570c5778b8`, cranelift)

The real module returns WRONG i64 values natively; this is not limited to the
`set` bool. Results by shape (reviewer probes in
`build/review-trait/{real,real2,asnt,col_nt}`):

- **SparseHash, ÷8 (`Dict<i64, T>` payload).** In the `nodes.spl` shape,
  `9000000000 -> 1125000000` and `7 -> 0`. A trait-free copy of the store
  shows the same ÷8 on the pre-fix (run 34) and post-fix Stage 2, which is the
  3-bit runtime-tag shift.
- **Embedded and Column, ×8 in a helper-parameter shape.** When the store
  values pass through a helper's `Result<i64, text>` parameter,
  `9000000000 -> 72000000000` and `-5 -> -40`.
- **Correct:** Column in the `nodes.spl` shape, and every `text` store
  (direct, column, sparse_hash).
- My own narrower probe (direct/column, values read in place) printed correct
  i64 values except `set` printing `1` for `Ok(true)`. That shape simply
  missed the ÷8 and ×8 paths.

Until this is fixed, `src/compiler/10.frontend/core/_AstExpr/nodes.spl`
gates the non-direct `SIMPLE_NODE_ATTR` / `SIMPLE_NODE_ATTR_SDN` placements
behind a fresh-store round-trip self-check. On a mismatch it prints
`node-attr: <placement> store failed its round-trip self-check on this build;
staying on direct storage (...)` and keeps mode 0.

- **llvm:** the build fails in codegen for `sha256`, `sdn.parser`,
  `data_schema_resolver` and `data_schema_core_v1` (llc error: `'%lN' defined
  with type 'i64' but expected 'ptr'`). The same llc failure in `sha256` and
  `sdn.parser` reproduces on the pre-fix Stage 2 with a trivial importer.
