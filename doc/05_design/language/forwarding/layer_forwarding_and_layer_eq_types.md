# Layer forwarding and layer-equivalent types

- **Status:** Design + first slice landed 2026-08-06
- **Feature:** compile-time layers, `@layer_eq` zero-cost type views (implicit by
  same field names, explicit via `@layer_field` rename tags), and forwarding as
  typed compiler metadata (`HirForwardDecl`) instead of generated source.
- **First slice landed:** `src/compiler/35.semantics/layer_eq_checker.spl` —
  the structural-equivalence proof engine + diagnostics, with fixtures and spec.

## 1. What exists today (surveyed, with anchors)

| Concern | Current reality |
|---|---|
| Forwarding | **Text-level desugar** in `src/app/desugar/forwarding.spl` (504 L). Four phases (`fn name = target`, `alias fn/me NAME = FIELD.METHOD`, `alias Trait = field`, blanket `alias field`) all **generate delegation source** before the parser sees it. Each generated method is a real call frame — precisely the physical-hop cost §5.3 of the perf plan wants erased. |
| Annotation passes | `@noalloc` is enforced by a dedicated semantic pass `src/compiler/35.semantics/noalloc_checker.spl` (registry of `NoallocFnEntry`, hard errors). This is the template for the layer-eq pass. |
| HIR expression pipeline | `10.frontend/parser_types_expr.spl` → `20.hir/hir_lowering/expressions.spl` → `35.semantics/resolve.spl` → `50.mir/_MirLoweringExpr/expr_dispatch.spl`. The MIR default arm (`expr_dispatch.spl:3380`) is a **loud** unsupported-kind failure — new HIR kinds cannot silently pass through. |
| AOP | `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` — facet/dynSMF design; logical join points (§6 of the perf plan) should extend it, not add a second interception system. |
| Layers | **Absent.** No `layer` keyword, no `@layer`, no `@layer_eq` anywhere in `src/compiler/`. |

## 2. Surface syntax

```
layer draw
layer gui uses draw
layer web uses gui, draw
layer wm  uses gui, draw

@layer(gui)
module gui.widgets
```

Rules: acyclic `uses` DAG; calls only same-layer or along a declared downward
edge; lower layers never import higher-layer semantic state; layers create no
runtime objects.

### Layer-equivalent types

Implicit (same field names, Ruby-like ergonomics — no boilerplate):

```
@layer_eq(draw.DeviceRect)
struct GuiDeviceRect:
    x: i32
    y: i32
    width: i32
    height: i32
```

Explicit rename tags where names differ:

```
@layer_eq(draw.DeviceRect)
struct GuiBounds:
    @layer_field(x)     left: i32
    @layer_field(y)      top: i32
    @layer_field(width)  extent_x: i32
    @layer_field(height) extent_y: i32
```

A conversion between proven-equivalent types is an **identity**: same SSA
value, same address, zero executable operations.

## 3. Equivalence proof obligations

Proven per pair, in this order (first failure reported with both sides):

1. field **count** equal
2. per-field **name** mapping total (same-name inference, or every field carries
   a `@layer_field` tag; a *partial* tag set is an error — no silent mixing)
3. per-field **type** identical (after alias resolution; no numeric widening)
4. per-field **offset** and **size** identical; total size and alignment equal
5. enum discriminant values equal
6. ownership/mutability class equal (value struct ↔ value struct only)
7. address space equal (host↔device is never equivalent)
8. **unit / space / color / alpha tags** equal (`@unit`, `@space`, `@color`,
   `@alpha`) — absent tag ≠ any tag

**Never equivalent** (must remain explicit operations): `CssLogicalRect` →
`DevicePixelRect` (scaling/rounding), straight → premultiplied color,
`HostBuffer` → `DeviceBuffer` (transfer), document → window point (transform),
UTF-8 byte offset → scalar index (indexing).

## 4. Typed forwarding: `HirForwardDecl`

The parser keeps the existing `alias` ergonomics but must emit metadata, not a
source body:

```
struct HirForwardDecl:
    logical_symbol: text
    receiver_projection: text     # field path, e.g. "draw"
    target_symbol: text
    layer_view_map: u32           # index into proven layer-eq view table
    effect_summary: u32
    logical_join_point_id: u32
```

Compile sequence (perf-plan §5.3): resolve layer DAG → prove layer-eq views →
build transitive forwarding graph → assign join-point IDs → weave static
aspects → specialize service table → **collapse forwarding chains** → erase
identity views → devirtualize single-target calls → inline/SROA → verify
`@noalloc`/`@copy_budget` → lower one physical call. AOP advice targets the
`logical_join_point_id`, so a business-logic-free wrapper need not exist
physically (extends the facet/dynSMF design above).

Gate per `@zero_forward_path` entrypoint: `physical_forward_calls = 0`,
`layer_view_copy_bytes = 0`; compilation fails if a claimed-identity view
changes size/alignment/ownership/address-space, allocates, copies, or calls a
user conversion.

## 5. First slice — landed

`src/compiler/35.semantics/layer_eq_checker.spl`: self-contained proof engine.
`LayerEqType` (name + ordered `LayerEqField{name, type_name, offset, size,
mapped_name}`) and `check_layer_eq(view, target) -> LayerEqVerdict` covering
obligations 1–4 plus the partial-tag-set rule, each rejection carrying a
`layer_eq` diagnostic naming both fields. Same-name inference and
`@layer_field` mapping both go through one mapping-resolution step, so the
implicit and explicit forms cannot drift.

Tests: `test/01_unit/compiler/semantics/layer_eq_checker_spec.spl` — accepted
same-name view, accepted full-rename view, rejected size mismatch, rejected
field-type mismatch, rejected partial tag set, rejected field-count mismatch.
Import path is `compiler.semantics.layer_eq_checker` (the `35.` numeric layer
prefix is stripped from the module namespace; `compiler.35.semantics.…` does
not resolve). Run under the **Rust seed** `bin/simple` (the only binary in
tree): `Results: 7 total, 7 passed, 0 failed`. Sabotage
was performed (type check skipped → rejection specs went red) and reverted.

## 6. Honestly deferred (concrete TODOs)

1. **Parser wiring** — `@layer_eq`/`@layer_field` are not yet parsed;
   annotations must flow through `10.frontend` decl parsing into a HIR-side
   registry the checker consumes (model: `noalloc_checker.spl`'s registry).
2. **`layer` declarations + DAG check** — DAG registry + cycle diagnostic +
   declared-upward rejection landed as `src/compiler/35.semantics/
   layer_dag_checker.spl` (M0, 2026-08-07), self-contained over synthetic
   `LayerDagRegistry` facts. Parser wiring of the `layer NAME [uses A, B]`
   keyword into `10.frontend` decl dispatch is still open — deferred as a
   separate follow-up (checked this session: `10.frontend/core/tokens.spl`
   has `TOK_KW_TRAIT`-style keyword tokens but the plan doc's file hint
   (`_ParserDecls/enum_module_body.spl`) does not itself contain the literal
   `"trait"`/`"struct"`/`"module"` strings, so the decl-dispatch site needs
   its own investigation before adding `layer`).
3. **Offset/size from real layout** — the checker consumes declared layouts;
   production wiring must feed it the compiler's actual layout computation, not
   fixture-declared numbers.
4. **`HirForwardDecl` emission** — retire the text-level generator in
   `src/app/desugar/forwarding.spl` phase-by-phase; keep it as fallback until
   collapse works, gated by the §4 zero-hop counters.
5. **Identity erasure in MIR** — needs a pure-Simple build to verify
   (`bin/simple` is the seed; the MIR default arm is loud, so a new HIR kind
   without its arm fails compile — safe to stage).
6. **Unit/space/color/alpha tags** (obligation 8) — parse + propagate;
   checker slot exists (`tag` field), semantics deferred with the tags.
