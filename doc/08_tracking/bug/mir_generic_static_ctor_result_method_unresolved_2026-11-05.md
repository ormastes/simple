# Method call on a struct built by a generic static constructor is unresolved in MIR

- **Status:** FIXED in source, PR work/mirp2-I. P2.
- **Found:** s3_fable43 (phase-3 P1 lead), family I2 ("methods on struct instances fail MIR lowering").
- **Layer:** 50.mir `_MirLoweringExpr/method_calls_literals.spl`, StaticMethod arm of `lower_method_call`.

## Exact failing shape
```
struct Box<T>:
    v: T
impl Box<T>:
    fn get() -> T: self.v
    static fn of(v: T) -> Box<T>: Box(v: v)
fn f() -> i64:
    val b = Box.of(4)
    b.get()          # also: Box.of(4).get()
```
`MIR: unresolved method call: get route=runtime-fallback key=::get owner= struct_method_syms=no`.
Probed and NOT failing: plain struct locals, `P(x:1)` literals, non-generic
static ctors, array elements, struct fields, free-fn results, for-loop and
if-val bindings, annotated `val c: Box<i64>`.

## Root cause
The StaticMethod arm only called `remember_call_hir_return`, whose Named-return
recovery needs a known concrete layout; a generic `Box<T>` has none, so the
result local had no `struct_value_syms` entry and the receiver owner was empty.
The Unresolved static arm already consulted `struct_method_return_names`
(`remember_method_return_provenance`); the StaticMethod arm now does the same
(canonical owner key, then plain owner name), only when no identity was recorded.

## Specs
`test/01_unit/compiler/50.mir/family_i_nil_payload_and_generic_static_ctor_spec.spl`
(2 RED before fix; 3 sibling-shape guards).
