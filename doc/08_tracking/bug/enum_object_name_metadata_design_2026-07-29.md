# Design: enum/struct name metadata for `rt_to_string` formatting

Status: design only (read-only investigation lane). No code changed.

## 0. Problem recap

`rt_to_string` (landed 57f402d, `src/runtime/runtime_native.c`) formats
tuple/array/dict/Option/Result correctly, but:

- Custom user **enums** fall through to `<value:0x..>` — the C runtime has no
  name table mapping `(enum_id, discriminant) -> (type name, variant name)`.
- **Structs** have no runtime-detectable representation at all — there is no
  `rt_struct_new`, no `RtCore*` struct type, no kind tag for a struct
  instance (confirmed: zero hits for `rt_struct|StructInstance` in
  `runtime_native.c`).

The interpreter oracle prints both correctly because the name info exists at
HIR/MIR time; it simply never reaches the C runtime as data.

## 1. Enum names — SMALL fix

### What already exists (compile-time)

`src/compiler/50.mir/mir_lowering_types.spl:225` and the lowering-context
initializer in `src/compiler/50.mir/_MirLowering/module_lowering.spl:143-146`
carry exactly the metadata needed, already fully populated per compile:

- `enum_runtime_id_index: Dict<text, i64>` — enum type name -> `enum_id`
  (`module_lowering.spl:197`, set by `register_enum_runtime_name` at
  `module_lowering.spl:188-197`). `enum_id` is
  `(hm_hash_text(runtime_name) % 2147483646) + 2` — a deterministic hash, so
  the runtime **cannot invert it back to a name**; a table is unavoidable.
- `enum_runtime_id_names: Dict<text, text>` — `"{enum_id}"` -> type name
  (same function), i.e. the reverse map, already built, per
  `module_lowering.spl:191-196` (with a collision check that already
  errors on hash collisions — good, no design work needed there).
- `enum_variant_index: Dict<text, [text]>` and
  `enum_variant_discriminants: Dict<text, [i64]>` — enum type name -> ordered
  variant names / discriminants, built in `register_enum_variants`
  (`module_lowering.spl:199+`).

All of this lives only in the in-memory lowering context (`lw`/`self`) and is
discarded after MIR lowering — it is never serialized into the compiled
artifact.

### Runtime side today

`src/runtime/runtime_native.c`:
- `RtCoreEnum` (line 818-826) already carries `enum_id: uint32_t` and
  `discriminant: uint32_t` — no name pointers, and this struct does **not**
  need to grow for the fix below (no ABI change).
- `rt_core_format_enum` (line 2613-2642) hardcodes id 0 = Result, id 1 =
  Option, and its own comment (line 2599-2612) already states the exact gap:
  "that name table ... is never emitted into the runtime binary as data".
- `rt_enum_new` (line 5039) and `rt_core_register_enum` (line 1075-1082) are
  the existing single choke-point / pointer-registry pattern used to make
  enum values runtime-detectable (built to fix a real SIGSEGV class, see the
  large comment at line 1036-1074) — this is the pattern to imitate for
  identity, not to modify.

### Construction call sites (where to emit the new calls)

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:
- ~line 1874-1933: `"Lower Shape.Circle(7) to rt_enum_new(enum_id,
  discriminant, payload)"` — general named-constructor call path, looks up
  `self.enum_runtime_id(enum_name)` at line 1896.
- ~line 1987-2030: sibling call path, same shape, also via
  `self.enum_runtime_id(enum_name)` at line 1988.
- ~line 182-250 is a **different, hardcoded id=1 (Option)** construction
  path (`enum_id_local = 1` at line 216) — do **not** touch; Option/Result
  stay on the existing hardcoded fast path in `rt_core_format_enum`.

Both real call sites already have `enum_name` (the type name) and the
variant's `variant.name` as compile-time string literals in scope at the
point `rt_enum_new` is emitted — the same literals the compiler already
knows how to lower to string data (this file already emits ordinary string
literals elsewhere; no new data-section or ABI mechanism is needed, unlike a
static rodata table + linker-visible symbol, which would be new machinery
this codebase does not currently have — no `.init_array`/ctor mechanism and
no case of runtime C code reading compiler-emitted globals via `extern` was
found in this codebase, so a call-based registration is the smaller, already
proven-safe route.)

### The fix

1. **Runtime** (`runtime_native.c`, near `rt_core_register_enum`/
   `rt_core_format_enum`): add two small functions backed by a plain
   idempotent hash map (key -> `RtCoreString*`), e.g.:
   - `void rt_register_enum_type_name(int64_t enum_id, int64_t name_ptr)`
   - `void rt_register_enum_variant_name(int64_t enum_id, int64_t discriminant, int64_t name_ptr)`
   Both no-op (or overwrite harmlessly — value is constant per type) on
   repeat calls, exactly like `rt_core_register_enum`'s
   "created at exactly one choke point, registered there" idiom but keyed by
   `(enum_id[, discriminant])` instead of pointer identity.
2. **Compiler** (`switch_operators_calls.spl`, the two sites above): right
   after emitting the existing `rt_enum_new(enum_id, discriminant, payload)`
   call, additionally emit calls to the two new runtime functions, passing
   the already-in-scope `enum_name` / `variant.name` string literals. Gate on
   `enum_id != 0 and enum_id != 1` so Option/Result — the hot path — are
   never touched.
3. **Runtime** (`rt_core_format_enum`, line 2639-2641): before falling
   through to `rt_core_nil()`, look up the two new tables; if both hit,
   format as `"{type_name}::{variant_name}({payload})"` (or bare
   `"{type_name}::{variant_name}"` if the variant is payload-less — needs a
   flag or a sentinel payload, mirroring how Option::None is distinguished
   today by discriminant alone at line 2619). If either lookup misses, keep
   the existing `<value:0x..>` fallback unchanged (fail-safe, purely
   additive — no existing behavior regresses).

### Cost / tradeoffs

Two extra calls + two hash-map inserts per **custom** enum construction
(Option/Result construction is completely unaffected by the gate above).
This is the same order of overhead the codebase already accepts for
dict/array/enum pointer registration. A construction-time registration is
technically redundant work if the same enum type is constructed millions of
times in a tight loop; if profiling later shows this matters, a fast-follow
can add a per-callsite "register once" static guard emitted by the compiler.
Ship the always-register version first — it is correct and simplest.

**Verdict: SMALL fix.** First concrete step: add
`rt_register_enum_type_name` / `rt_register_enum_variant_name` to
`runtime_native.c` (+ 2 `extern fn` declarations on the compiler side) and
wire them into the two `rt_enum_new` call sites already identified in
`switch_operators_calls.spl` (~1874-1933, ~1987-2030), then extend
`rt_core_format_enum`'s fallback branch (line 2639-2641).

## 2. Struct/object printing — assessment

### Current state

No struct heap representation exists in the C runtime at all — confirmed by
grep (`rt_struct_new`, `RtCoreStruct`, `StructInstance`: zero hits). A
comment in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1029`
— *"an array/dict/struct handle unboxed from..."* — indicates struct
instances ARE heap pointers at runtime today, but with no controlled kind
byte: the first bytes at the pointer are just the raw first field's value,
not a tag. That means a struct pointer boxed into `Any` is genuinely
undetectable, and worse, unsafe to probe blindly — this is exactly the class
of bug the enum/dict/array pointer registries (`rt_core_register_enum` etc.,
`runtime_native.c:1036-1074`) were built to eliminate for a flat i64 that
merely *aliases* the `TAG_HEAP` bit pattern. Reading an arbitrary struct's
first byte as a "kind" would reopen that exact hazard.

This pass did **not** locate the actual struct-allocation choke point(s) in
codegen (a grep for `rt_alloc|struct_alloc|StructNew` in
`core_codegen.spl` came up empty — struct construction is emitted elsewhere,
not audited in this design-only pass). Locating every construction site is
the required first step before committing to an implementation timeline.

### Two design options

**(a) In-band header — real ABI change.** Prepend an
`{kind, flags, reserved, type_id: uint32_t}` 8-byte header before struct
field data, mirroring `RtCoreArray`/`RtCoreEnum`. This changes every
struct's in-memory layout: every field-offset computed anywhere in codegen
shifts by the header size, and any FFI/native-interop boundary that assumes
a struct's raw bytes start at field 0 (a real risk for a compiler whose
stated default is C/Rust interop) breaks. **Cost: LARGE**, cross-cutting
through codegen, FFI boundaries, and possibly compiled-artifact caches.

**(b) Out-of-band pointer registry — no ABI change (recommended).** Mirror
the exact `rt_core_register_scoped_immortal` pattern already used for
enum/dict/array/mutex pointer membership (`runtime_native.c:940-1082`): add
`rt_core_register_struct_instance(ptr, type_id)`, called once at each struct
construction choke point, storing `ptr -> type_id` in a hash map. Struct
layout is **completely untouched**. Detection becomes "is this pointer a
member of the struct registry" — the same pure-pointer-comparison-before-
dereference idiom that already fixed a real SIGSEGV in this exact area
(`rt_core_is_registered_enum`, line 1080-1082). A `type_id -> (type_name,
[field_name...])` table is then built exactly like the enum name table in
§1. This is feasible **without** an ABI change, provided the number of
construction choke points is small and enumerable — unverified in this pass.

### Verdict

**Feasible without an ABI change via option (b)**; option (a) would require
one and is not recommended. Cost is **medium-to-large** regardless of
option, dominated by two unknowns this design pass could not resolve:
(1) how many distinct struct-construction sites exist across all codegen
backends (the LLVM-ish `_MirToLlvm` path and the native/`70.backend/backend/
native` path may each construct structs independently — both need the
registration call), and (2) whether field-name ordering is stable and
available at each site the same way `enum_name`/`variant.name` are at the
enum sites in §1. Recommend scoping struct printing as **Phase 2**, gated on
a follow-up audit of the construction choke point(s) — do not attempt to
land it in the same change as the enum fix.

## 3. Overlap / sequencing with pending work

- `runtime_native.c` is an actively-edited hot file — the aggregate
  formatter itself just landed there (57f402d). Both the enum-name additions
  (§1) and the struct-registry additions (§2) land in the **same
  neighborhood**: `rt_core_format_enum` and the `rt_core_register_*` family
  immediately above it. Re-read the "IMPORTANT LIMITATION" comment at line
  2599-2612 before editing — it explicitly documents the current behavior
  this change supersedes and will need rewriting, not just appending to.
- `switch_operators_calls.spl`'s construction sites (§1) are read by
  `expr_dispatch.spl` via the same `enum_variant_index` /
  `enum_runtime_id_index` Dicts (10+ call sites, e.g.
  `expr_dispatch.spl:371,1453,1535,1536,1658,1668,1762,2914,2916,3052,3071`
  and `method_calls_literals.spl:1032,1034`). The enum-name fix reads these
  Dicts one more time but does not mutate them, so risk of interference is
  low — but any concurrent refactor of `expr_dispatch.spl`'s enum
  classification logic should land before or after, not interleaved with,
  this change.
- `bootstrap_globals.spl` (lines 120, 279, 487, 519-527, 591, 625-633) keeps
  a **parallel bootstrap-only copy** of the Option/Result variant tables
  (`_bootstrap_enum_runtime_id_names`, etc.) for the seed-compiler path.
  Since §1 explicitly excludes `enum_id` 0/1, bootstrap parity is
  unaffected — but flag this for whoever implements, so Option/Result don't
  get accidentally double-registered on top of `rt_core_format_enum`'s
  existing hardcoded handling.

## 4. Recommended minimal first step

Implement **§1 (enum names) only**. It is additive, touches two files, adds
no new struct/ABI/data-section machinery, keeps Option/Result untouched, and
fails safe (unresolved lookups keep today's `<value:0x..>` fallback).
Struct/object printing (§2) should wait for a dedicated audit of
struct-construction choke points across both codegen backends before any
implementation estimate is trusted.

## Phase-2 struct-construction audit (2026-07-29)

Read-only follow-up audit locating the struct-construction choke point(s)
requested in §2/§4. No code changed.

### 1. HIR/MIR lowering: SINGLE choke point

- `HirExprKind.StructLit` (declared `src/compiler/20.hir/hir_definitions.spl:498`,
  produced by `src/compiler/20.hir/hir_lowering/expressions.spl:800-809`) is
  **never matched anywhere in `src/compiler/50.mir/`** — grepped the whole
  tree (`_MirLowering/`, `_MirLoweringExpr/`, `hwir/`, `mir/`, top level):
  zero `case StructLit` arms. That HIR variant appears to be dead in the
  MIR-lowering path; it may only be reachable through the interpreter
  (`95.interp`), not audited here.
- The **live** path is constructor-call syntax `Point(x:3, y:4)`, which HIR
  lowers to a plain `Call`. MIR lowering's call-classification code at
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3105-3107`
  checks `self.struct_field_order.has(direct_name)` and, if true, routes to:
  - **`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2052`**
    — `me lower_struct_construct(symbol: SymbolId, struct_name: text, args: [HirCallArg]) -> LocalId`.
    This is the **single MIR-lowering choke point** for every struct
    instance built via constructor syntax (the docstring at line 2053-2056
    states it also covers `Point{...}` brace syntax, i.e. it's meant to be
    the one place both forms converge). Only one call site exists
    (line 3107); grepped for other callers, none found.
  - Inside it, the pointer-producing MIR instruction is emitted at
    **line 2272**: `b.emit_aggregate(AggregateKind.Struct(canonical_symbol), ops, struct_ty)`.

### 2. Backend codegen: SCATTERED (one site per backend)

`AggregateKind.Struct` is consumed independently by each backend — not a
single choke point once past MIR:

- **LLVM backend** — `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:58-95`
  (`translate_aggregate`, `case Struct(_):`). Heap pointer is produced at
  **line 84**: `{agg} = call ptr @rt_alloc(i64 {n * word_bytes})`, followed
  by a per-field GEP+store loop (lines 85-90), then the dest local is
  aliased to `agg` via a 0-offset GEP (line 94).
- **Cranelift backend** — `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:620-633`
  (`case Struct(_):`). Heap pointer is produced at **line 622**:
  `base = translate_runtime_import_call_i64(ctx, cl_module, "rt_alloc", [size])`,
  then a per-field store loop (624-627), then a heap-tag bit is OR'd in
  (line 628-629) before binding to `dest.id`.
- Both call the same runtime primitive (`rt_alloc`, `src/runtime/runtime_native.c:3771`)
  but each backend has its own emission code — an injected
  `rt_register_object_type(ptr, type_id)` call needs to land in **both**
  backend sites (2 call sites total, not N). This is a small, enumerable
  set, not truly "scattered" in the sense of many unpredictable sites.

### 3. Type-name / field-name availability at the choke points

- **`lower_struct_construct`** (MIR choke point) has, as direct parameters
  or locals already in scope: `symbol: SymbolId` (unique per struct decl,
  underlying repr is a plain `i64` — `struct SymbolId: id: i64` at
  `src/compiler/20.hir/hir_types.spl:66-68`, directly usable as an
  `object_type_id` with **no new ID scheme needed**), `struct_name: text`
  (the type name), and `field_names = self.struct_field_order[struct_name]`
  (declared field-name list, in field order, line 2057) — i.e. everything
  an `enum_id`-style registration would need is already local at this exact
  point. `AggregateKind.Struct(canonical_symbol)` carries the `SymbolId`
  through to both backends untouched, so the backend sites also have the
  type id for free without re-deriving it; they do NOT have `struct_name`/
  field names directly (those live in the MIR-lowering `struct_field_order`
  / `struct_field_type_name` Dicts, keyed by name, not currently threaded
  into the backend's per-instruction data) — a name/field table would need
  to be emitted once per struct type (e.g. at module-lowering time) and
  looked up by `SymbolId` at print time in the C runtime, mirroring how
  `enum_id` tables are proposed in §1, rather than re-passed at every
  construction site.
- No `object_type_id` scheme currently exists for structs (`SymbolId` is a
  compile-time-only concept; nothing propagates it into the compiled binary
  today). It would need to be assigned/exported the same way §1 proposes
  doing for `enum_id`.

### 4. Runtime heap-kind confirmation

Grepped `src/runtime/runtime_native.c`: no `rt_struct_new`, no
`StructInstance`, no `RT_VALUE_HEAP_OBJECT` — confirmed absent. Struct/tuple
instances are untyped `rt_alloc`'d word arrays with **no runtime metadata or
kind tag at all**, unlike array/dict/enum/closure which each call
`rt_core_register_scoped_immortal` (e.g. lines 983, 992, 1077, 1136, 1470) to
register into the scoped-immortal tracking table. `rt_alloc` itself
(line 3771) only does raw transient-allocation bookkeeping
(`rt_core_transient_raw_register`), nothing type-aware. This matches the
design doc's premise in §2: an out-of-band `ptr -> type_id` registry piggy-
backed on the same `rt_core_register_scoped_immortal`-style idiom is
structurally consistent with how the other heap kinds already register
themselves, and there is no competing/duplicate mechanism to avoid.

### Recommended minimal injection point

Two call sites, not one, because MIR has a single lowering choke point but
two codegen backends: `aggregate_intrinsics.spl:84` (right after the
`rt_alloc` call, before the field-store loop) and
`cranelift_codegen_adapter.spl:622` (same position). Both already have the
heap pointer (`agg`/`base`) and the `SymbolId` (via `AggregateKind.Struct`'s
payload) in scope at that line — no new plumbing needed to reach the
pointer+type-id pair; only the type-id -> name/field-list table (built once,
likely at module-lowering time from `struct_field_order`) is new work.
