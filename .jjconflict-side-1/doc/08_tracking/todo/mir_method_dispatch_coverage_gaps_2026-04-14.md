# MIR Method-Dispatch Qualification — Remaining Coverage Gaps (2026-04-14)

**File under audit:** `src/compiler_rust/compiler/src/mir/lower/lowering_expr.rs`
**Helper:** `recover_receiver_type` (line ~38), called from `HirExprKind::MethodCall` at line ~1412 / ~1496.
**Related companion spec:** `test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl`
(failing-placeholder `it` blocks, one per gap — cross-reference each H# heading).

---

## 1. Background

The Rust-bootstrap compiler qualifies MIR method calls using the *type-name* of
the receiver (`"<TypeName>.<method>"`). When the receiver's own `expr.ty` is
`Any` or otherwise unnamed (common for cross-module constructors whose return
type inference fell through to `Any`), `get_type_name` returns `None` and the
call is emitted as the bare `.method` symbol. The native-build codegen then
picks the *shortest-named* `.method` in the module, producing silent
mis-dispatches (`shell.init()` → `Ps2Keyboard.init`, sys-gui-006 Blocker 2).

`recover_receiver_type` walks one structural hop into the receiver
sub-expression to recover a usable `TypeId` from `TypeRegistry`. Current
coverage:

| Variant | Covered? | Landed in |
|---|---|---|
| `HirExprKind::Local(idx)` | yes | `f940740f` (Round-16 fix) |
| `HirExprKind::FieldAccess { receiver, field_index }` | yes | `9cef02b8` (Round-17) |
| `HirExprKind::Index { receiver, .. }` | yes | `9cef02b8` (Round-17) |
| Tuple projections (via `FieldAccess` on `HirType::Tuple`) | yes | `9cef02b8` (Round-17) |
| **All other `HirExprKind` variants** | **no — falls through to `_ => None`** | — |

The `_ => None` arm means: whenever the receiver is anything other than
Local / FieldAccess / Index **and** its own `receiver.ty` is unnameable, the
MIR call is emitted unqualified and the native backend mis-dispatches.

---

## 2. Coverage Audit — HirExprKind Variants

Enumerated from `src/compiler_rust/compiler/src/hir/types/expressions.rs`
(`pub enum HirExprKind`).

Legend:
- **COVERED**  — handled by `recover_receiver_type`
- **N/A**      — cannot syntactically be a method-call receiver, or always
                 produces a named type in practice
- **GAP**      — *can* receive a method call, falls into `_ => None`

| # | Variant | Status | Notes |
|---|---|---|---|
| 1 | `Integer(i64)` | N/A | Literal has named type `i32/i64/etc.` |
| 2 | `Float(f64)` | N/A | Named type |
| 3 | `String(String)` | N/A | Named type |
| 4 | `Bool(bool)` | N/A | Named type |
| 5 | `Nil` | N/A | Cannot method-dispatch on nil |
| 6 | `Local(idx)` | COVERED | Round-16 |
| 7 | `Global(name)` | **GAP G1** | `Module.Singleton.method()` |
| 8 | `Binary { op, left, right }` | N/A | Returns primitives/bool |
| 9 | `Unary { op, operand }` | **GAP G2** | `(-vec).normalize()` — operator overload chains |
| 10 | `Call { func, args }` | **GAP G3 (HIGH)** | `factory().init()`, `make()::new().run()` |
| 11 | `MethodCall { receiver, method, args, dispatch }` | **GAP G4 (HIGH)** | `a.make().init()` — chained method calls |
| 12 | `FieldAccess { receiver, field_index }` | COVERED | Round-17 |
| 13 | `Index { receiver, index }` | COVERED | Round-17 |
| 14 | `Tuple(Vec<HirExpr>)` | N/A | `(a, b).method()` not idiomatic; builder projects fields first |
| 15 | `Array(Vec<HirExpr>)` | N/A | Literal, not a receiver |
| 16 | `ArrayRepeat { value, count }` | N/A | Literal |
| 17 | `VecLiteral(Vec<HirExpr>)` | N/A | Literal |
| 18 | `StructInit { ty, fields }` | **GAP G5** | `Widget { ... }.init()` — type is in the kind itself |
| 19 | `Dict(pairs)` | N/A | Runtime map literal |
| 20 | `If { cond, then, else }` | **GAP G6** | `(if flag then a else b).method()` |
| 21 | `Ref(inner)` | **GAP G7** | `(&obj).method()` — rare; usually auto-deref |
| 22 | `Deref(inner)` | **GAP G8 (HIGH)** | `(*ptr).method()` — T63 flagged |
| 23 | `PointerNew { kind, value }` | N/A | `new &T(v)` has named type `*T/&T` |
| 24 | `Cast { expr, target }` | **GAP G9** | `(x as DerivedT).method()` — target is a known TypeId |
| 25 | `Lambda { params, body, captures }` | **GAP G10 (HIGH)** | Closure-capture receiver — T63 flagged |
| 26 | `Yield(value)` | N/A | Returns to driver |
| 27 | `GeneratorCreate { body }` | N/A | Produces Generator; method calls have named ty |
| 28 | `FutureCreate { body }` | N/A | Produces Promise; named ty |
| 29 | `Await(future)` | **GAP G11** | `future.await.method()` — awaited value type |
| 30 | `ActorSpawn { body }` | N/A | Produces Actor ref; named ty |
| 31 | `BuiltinCall { name, args }` | N/A | Prelude builtins return named types |
| 32 | `ContractResult` | N/A | Only in contract blocks; `ensures` has typed `result` |
| 33 | `ContractOld(inner)` | **GAP G12 (LOW)** | `old(obj).method()` in ensures; rare |
| 34 | `GpuIntrinsic { intrinsic, args }` | N/A | Returns SIMD/primitive |
| 35 | `LetIn { local_idx, value, body }` | **GAP G13** | `(let x = ... in x).method()` — body's `.ty` |
| 36 | `NeighborAccess { array, direction }` | N/A | SIMD lane value |

---

## 3. Gap Detail — Repros & Fix Approach

Each gap lists (a) a minimal `.spl` repro, (b) the recovery strategy, (c)
estimated LoC for the `recover_receiver_type` match arm.

Two classes with an ambiguous `init()` are used so mis-dispatch is
observable at runtime (shorter-named class wins the bare-symbol lottery).
The canonical template is:

```spl
class A:
    value: i64
    static fn new() -> A: A(value: 0)
    me init(): self.value = 701

class B:
    tag: i64
    static fn new() -> B: B(tag: 0)
    me init(): self.tag = 802
```

### G1 — `HirExprKind::Global(name)` (priority: **MEDIUM**, ~10 LoC)
**Repro:**
```spl
static global SHELL: A = A.new()
SHELL.init()   # should hit A.init; bare-name may hit B.init
```
**Fix:** Look up the symbol name in the module's `globals` table (already
reachable from `self.hir_module`) and return `globals.get(name).map(|g| g.ty)`.

### G2 — `HirExprKind::Unary { operand, .. }` (priority: **LOW**, ~5 LoC)
**Repro:** `(-vec3).normalize()` where `Vec3` overloads `neg`.
**Fix:** Recurse into `operand` — unary operators on user types preserve
the operand's type (ops like negation/not don't change class identity).
`recover_receiver_type(operand)`.

### G3 — `HirExprKind::Call { func, args }` (priority: **HIGH**, ~15 LoC)
**Repro:**
```spl
fn make_a() -> A: A.new()
make_a().init()
```
**Fix:** The callee's return type is the receiver type. Resolve `func` as:
- `HirExprKind::Global(name)` → look up function in `hir_module.functions`,
  return its declared `ret_ty`.
- Otherwise fall back to `func.ty` (function type's return slot via
  `HirType::Function { ret, .. }`).

### G4 — Chained `MethodCall` (priority: **HIGH**, ~20 LoC)
**Repro:**
```spl
class Factory:
    me make_a() -> A: A.new()
var f: Factory = Factory.new()
f.make_a().init()
```
**Fix:** The qualified MIR function symbol (`"Factory.make_a"`) has a known
return type in the MirFunction signature table. Resolve method via the
same qualification logic the MethodCall dispatch already uses, then look up
the MIR function's return TypeId. If the inner method is itself unqualified,
recurse — terminates at a Local or a named type.

### G5 — `HirExprKind::StructInit { ty, fields }` (priority: **MEDIUM**, ~3 LoC)
**Repro:** `A { value: 0 }.init()`
**Fix:** Trivial — the kind already carries `ty: TypeId`. Return `Some(*ty)`.

### G6 — `HirExprKind::If { then, else, .. }` (priority: **MEDIUM**, ~8 LoC)
**Repro:**
```spl
var a: A = A.new()
var b: A = A.new()
(if flag then a else b).init()
```
**Fix:** Both branches must unify to a common type. Call
`recover_receiver_type(then_branch)`; if `None`, try `else_branch`. The HIR
If's own `expr.ty` is usually populated but set to `Any` under the same
cross-module constructor path — hence this fallback.

### G7 — `HirExprKind::Ref(inner)` (priority: **LOW**, ~6 LoC)
**Repro:** `(&widget).init()` with explicit ref (unusual; auto-ref covers
most cases).
**Fix:** Recurse into `inner`, then wrap the result in a
`HirType::Pointer { inner: recovered, kind: Ref, .. }` looked up in the
registry. In practice the existing `FieldAccess`/`Index` arms already
strip one pointer layer, so returning `recover_receiver_type(inner)`
(the inner, un-wrapped type) is sufficient for dispatch purposes.

### G8 — `HirExprKind::Deref(inner)` (priority: **HIGH**, ~8 LoC) — **T63-flagged**
**Repro:**
```spl
var ptr: *A = new *A(A.new())
(*ptr).init()
```
**Fix:** Recurse into `inner` to recover the pointer's TypeId, then unwrap
one `HirType::Pointer { inner: pointee, .. }` layer via `TypeRegistry`.
Mirrors the existing pointer-strip logic in the `FieldAccess` / `Index`
arms.

### G9 — `HirExprKind::Cast { expr, target }` (priority: **MEDIUM**, ~3 LoC)
**Repro:** `(some_any as A).init()`
**Fix:** Return `Some(*target)` — the cast's target TypeId is authoritative.

### G10 — `HirExprKind::Lambda` captured receiver (priority: **HIGH**, ~25 LoC) — **T63-flagged**
**Repro:**
```spl
var a: A = A.new()
var run = || a.init()   # `a` is captured; inner `a` is Local(capture_idx)
run()
```
Note: the mis-dispatch surfaces at the captured `Local` *inside the
lambda body*, not at the `Lambda` expression itself. When the lambda is
MIR-lowered, its `captures: Vec<usize>` maps into synthetic local slots
of the generated closure function. If the enclosing function's local
table has a named type but the closure's capture slot does not, the
inner `a.init()` — a `Local(captured_slot)` — falls through.

**Fix:** During lambda lowering (`HirExprKind::Lambda` arm, line ~415),
propagate the enclosing-function local's TypeId into the synthesized
closure function's `params` / `locals` entries so the existing
`Local(idx)` arm in `recover_receiver_type` finds a named type. No new
arm needed — this is a lambda-lowering fix, not a receiver-recovery one.
Listed here because it shares the same failure mode (bare-name
mis-dispatch) and the same diagnosis (SIMPLE_DEBUG_METHOD_DISPATCH=1).

### G11 — `HirExprKind::Await(future)` (priority: **MEDIUM**, ~12 LoC)
**Repro:**
```spl
async fn make_a_async() -> A: A.new()
(await make_a_async()).init()
```
**Fix:** Recover `future`'s TypeId via `recover_receiver_type(future)`,
then unwrap one `HirType::Promise { inner, .. }` layer (or `Future`) via
`TypeRegistry`, returning the inner TypeId.

### G12 — `HirExprKind::ContractOld(inner)` (priority: **LOW**, ~3 LoC)
**Repro:** `ensures: old(self).method() == ...`
**Fix:** `recover_receiver_type(inner)` — `old()` preserves the inner
expression's type.

### G13 — `HirExprKind::LetIn { body, .. }` (priority: **LOW**, ~3 LoC)
**Repro:** Produced internally by match-lowering:
```spl
match x:
    case Some(a): a.init()
```
The `a` receiver is a Local inside a LetIn body, so the Local arm already
fires. Direct surface-syntax `(let x = e in x).method()` isn't
user-writable today, but the LetIn node can appear in lowered position
if future sugar desugars to it.
**Fix:** `recover_receiver_type(body)` — the let-in's value is the body's
value.

---

## 4. Priority Ranking

| Rank | Gap | Why |
|---|---|---|
| P0 | **G8 Deref** | T63 agent explicitly flagged. `*ptr` is pervasive in baremetal / FFI code (shell, kernel, driver lanes). |
| P0 | **G10 Closure capture** | T63 flagged. Callback-heavy GUI and actor code relies on lambdas capturing receivers. |
| P1 | **G3 Call** | `factory_fn().init()` is common in builder / DI patterns. Blocks direct idioms with no workaround shorter than an explicit `var tmp: T = factory_fn()`. |
| P1 | **G4 Chained MethodCall** | `builder.make().run()` is idiomatic. Same workaround cost as G3. |
| P2 | G1 Global, G5 StructInit, G6 If, G9 Cast, G11 Await | Each covers a real pattern but has cheap user workaround (bind to a typed local first). |
| P3 | G2 Unary, G7 Ref, G12 ContractOld, G13 LetIn | Rare; workaround is trivial. |

**Combined estimate:** ≈ **120 LoC** for the `recover_receiver_type` match
arms + **≈ 25 LoC** for the G10 lambda-lowering propagation. Plus ~10
LoC of matching per-gap test assertions in
`method_dispatch_uncovered_gaps_spec.spl`.

---

## 5. Recommended Landing Order

1. **G5 StructInit** (3 LoC) — trivial, warm-up diff; proves the spec
   harness rejects bare-name dispatch.
2. **G9 Cast** (3 LoC) — equally trivial; both unblock diagnostic
   iteration.
3. **G8 Deref (P0, T63)** — unblocks baremetal shell/kernel lanes.
4. **G3 Call + G4 Chained MethodCall** — builder idioms.
5. **G10 Lambda capture (P0, T63)** — needs lambda-lowering diff, larger
   scope than the rest; land last in its own commit with a regression
   spec.
6. Remaining P2/P3 items as cleanup pass.

Each landing should:
- Add / un-skip the matching `it` in
  `test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl`.
- Run with `SIMPLE_DEBUG_METHOD_DISPATCH=1` and verify the compile-time
  dump no longer shows the repro's bare-name entry.
- Keep `recover_receiver_type` side-effect-free (lookups against
  `TypeRegistry` only — no synthesis).

---

## 6. Diagnostic Aid

`SIMPLE_DEBUG_METHOD_DISPATCH=1` at compile time dumps every unqualified
MIR method call with its source span. Run on a repro from section 3 to
confirm the gap *before* and its absence *after* each fix.

## 7. Cross-References

- Round-16 fix commit: `f940740f` (`fix(codegen): qualify MIR method
  calls via MirLocal type when receiver.ty is unnamed`)
- Round-17 fix commit: `9cef02b8` (`fix(codegen): widen MIR method
  dispatch qualification to field/tuple/index receivers`)
- Round-18 loudness: `56f7a618` (`fix(codegen): make me-method body
  codegen failures loud + opt-in hard error`)
- T63 agent flag: Deref + closure-capture gaps
- Existing specs: `test/unit/compiler/codegen/baremetal_method_dispatch_spec.spl`,
  `test/unit/compiler/codegen/method_dispatch_field_access_spec.spl`
