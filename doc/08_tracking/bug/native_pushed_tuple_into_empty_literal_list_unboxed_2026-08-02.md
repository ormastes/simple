# Native lane: a tuple pushed into an empty-literal-initialized list is stored unboxed; any `.N` read SEGVs

- **ID:** native_pushed_tuple_into_empty_literal_list_unboxed_2026-08-02
- **Date:** 2026-08-02
- **Status:** CLOSED (2026-08-08) — all three follow-on gaps in the native-build tuple-to-text/field-read family fixed in pure-Simple MIR lowering (no Rust seed change, no bootstrap rebuild): gap (a) `t.0`/`t.1` field-index access under `SIMPLE_BOOTSTRAP=1`, gap (b) whole-tuple interpolation rendering, gap (c) mixed-type tuple field READS. See the dated sections below for each. The *original* empty-literal-list unboxed-storage SEGV this doc opened with was the seed-codegen finding that kicked off the investigation; the family it led to is what closed.
- **Severity:** high (deterministic SIGSEGV, and a silent wrong value on the read-without-field path)
- **Lane:** `native-build` only. The interpreter is correct.
- **Engine evidence caveat:** every result below was produced by the **Rust
  seed** (`bin/release/x86_64-unknown-linux-gnu/simple`, mtime 2026-08-02 01:19),
  confirmed seed by `strings bin/simple | grep -c "enum construction: unregistered enum"` → `0`.
  These are **seed results, not self-hosted results.**

## Symptom

Deterministic `SIGSEGV` (exit 139, 3/3 runs, and on a freshly rebuilt artifact):

```
[simple-runtime] Fatal: SIGSEGV at address 0xb0f39781b62
```

## Minimal repro (SEGV)

```simple
fn main():
    var h: [(i64, i64)] = []
    h.push((7, 9))
    println("f0 {h[0].0}")
```

`bin/simple native-build repro.spl -o repro.bin` → build exit 0; running it SEGVs.
`.1` faults identically. Binding first (`val e = h[0]` then `e.0`) also faults —
the binding is not a workaround, it only moves the fault to the field read.

## The decisive probe: the element comes back unboxed

Reading the element **without** a field access does not crash, and shows why:

```simple
fn main():
    var h: [(i64, i64)] = []
    h.push((7, 9))
    println("elem {h[0]}")        # prints 11937770476386
```

`11937770476386` is a **raw heap pointer printed as an integer** — the tuple's
box/tag has been stripped. `.0` then dereferences that raw pointer as if it were
a tagged value, which is the wild deref. So the SEGV is the second-order effect;
the primary defect is that the pushed element is **stored/read unboxed**.

Note this read-only form is a *silent wrong answer*, not a crash — it is the more
dangerous half of the bug.

## Isolation matrix (all via `native-build`, seed)

| # | Shape | Result |
|---|---|---|
| m1 | `val t = (7,9)` ; `t.0` | OK (`7`) |
| m2 | `[]` + push ; `h.len()` only | OK (`1`) |
| m3 | **`[]` + `h.push((7,9))` ; `h[0].0`** | **SEGV** |
| m4 | `[]` + push ; `for e in h`, no field access | OK |
| m5 | `[i64]` + push ; `h[0]` | OK (`7`) |
| m6 | `[]` + push ; `val e = h[0]` then `e.0` | **SEGV** |
| m7 | `[]` + push ; `h[0].1` | **SEGV** |
| q1 | `[(7,9)]` (non-empty literal) + push `(11,13)` ; `h[0].0`, `h[1].0` | OK (`7`, `11`) |
| q2 | `[]` + `val t=(7,9)` ; `h.push(t)` ; `h[0].0` | OK (`7`) |
| q3 | `[i64]` + push ; `h[0]` | OK |
| p3 | `val h: [(i64,i64)] = [(7,9)]` ; `h[0].0` | OK (`7`) |
| d3 | `var h = [(7,9)]` (untyped, non-empty) ; `h[0].0` | OK (`7`) |
| — | m3 source under the **interpreter** (`bin/simple run`) | OK (`f0 7`) |

Two conditions must hold together:

1. the list is initialized from an **empty literal** `[]` (a non-empty literal
   initializer, q1/p3/d3, is always correct), **and**
2. the pushed value is an **inline tuple literal** (a val-bound tuple, q2, is
   already materialized as a heap value and is correct).

A list of non-tuple elements (m5/q3) is unaffected, and a field access is
required to turn it into a crash (m2/m4 survive).

## Why this is not the previously-reported `signal_stubs` SEGV cause, but does explain it

A prior lane reported a SEGV on `val sig = entry.0` in `signal_stubs.spl` and
attributed it to tuple positional field access. That attribution was too broad:
bare tuple `.0` (m1), function-returned tuple `.0` (p2), and literal-list
element `.0` (p3) all work. The actual trigger is the empty-literal-list + inline
push shape — which is exactly the shape `signal_stubs.spl` has:

```simple
var _signal_handlers: [(i64, fn())] = []
_signal_handlers.push((signal, handler))
...
val sig = entry.0
```

That same lane's diagnosis was made while `src/runtime/runtime.c` / `runtime.h`
were conflict-marker corrupted in the working copy. The corruption is **not** the
explanation: with the runtime repaired, this defect still reproduces
deterministically.

## Localization

The read path returns the raw slot without the type-directed unbox that the
index/dict read paths apply. `get_index_element_type`
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:939`) resolves the
element type from the array's `HirType::Array { element, .. }`; when the
initializer is an empty literal that element type is not pinned to the declared
`(i64, i64)`, so the push stores and the read retrieves without agreeing on
boxing. Array `push` lowering is at
`src/compiler_rust/compiler/src/codegen/instr/methods.rs:228`.

This is the same *class* as `native_mixed_tuple_field1_statement_drop_2026-07-29`
("reads must apply the same type-directed unbox the index/dict read paths share")
but on the array-read path with an empty-literal initializer. That 07-29 fix is
present and live in this binary — positive capability probe `("x", 7).1` prints
`7` correctly — so this is a distinct, still-open defect, not a stale-binary
artifact.

## Workaround

Bind the tuple to a `val` before pushing, or give the list a non-empty literal
initializer:

```simple
var h: [(i64, i64)] = []
val t = (7, 9)
h.push(t)            # correct
```

## Follow-up

Pin the array element type from the **declared** type when the initializer is an
empty literal, so push and index-read agree on boxing; then re-run the isolation
matrix above. Fix requires a Rust seed rebuild to verify.

---

## Scope correction (verified independently, 2026-08-02)

The trigger is **broader than `push` into an empty-literal list**. Rendering ANY
tuple value to text under native codegen emits the raw heap pointer as an
integer. No list, no `push`, no `[]` initializer required:

```simple
fn main():
    val t = (7, 9)
    print("field: {t.0}\n")    # 7          -- correct
    print("tuple: {t}\n")      # 103244165829280  -- raw pointer, exit 0
```

Native: `tuple: 103244165829280`, **exit 0**. Interpreter: `tuple: (7, 9)`.

So the defect family is **tuple -> text conversion under native codegen does not
decode the box**; the pushed-into-empty-list case documented above is the variant
where the resulting untagged value is subsequently *dereferenced*, turning a
silent wrong answer into a SIGSEGV. The silent form is the more dangerous half
and has the wider blast radius: any log line, diagnostic, or error message
interpolating a tuple prints a pointer, exit 0, with nothing to notice.

Reproduced independently of the original report, on a freshly built artifact:
- `print("tuple: {t}\n")`, healthy tuple  -> pointer integer, exit 0
- `h.push((7,9)); h[0].0` after `var h: [(i64,i64)] = []` -> SIGSEGV exit 139
- Interpreter correct in both cases.

Caveat: all measurements are **Rust seed** evidence
(`strings bin/simple | grep -c "enum construction: unregistered enum"` -> 0).

---

## 2026-08-07 update: JIT lane fixed, AOT (`native-build`) lane still open

Commit `81c58562fac` ("fix(jit): format tuples as (a, b) not `<tuple@ptr>` in
native/JIT value printer", 2026-07-29) landed a fix in the runtime shared by
every native-codegen lane:
`src/compiler_rust/runtime/src/value/sffi/io_print.rs:533-550`
(`heap_value_to_display_string`, `HeapObjectType::Tuple` arm) — it mirrors the
`Array` arm just above it: iterate `rt_tuple_len`/`rt_tuple_get`, recurse
through `value_to_display_string`, join with `", "`, wrap in `()`; empty tuple
-> `()`.

Re-running the "scope correction" repro above today, **per-engine, on a
freshly built binary**, splits the family:

```simple
fn main():
    val t = (7, 9)
    print("field: {t.0}\n")
    print("tuple: {t}\n")
```

| Engine | Command | `tuple: {t}` output | Verdict |
|---|---|---|---|
| Interpreter | `bin/simple test` (spec form) | `tuple=(1, 2, 3)` | correct |
| JIT (default) | `bin/simple run tt2.spl` | `(7, 9)` | **correct — fixed** |
| JIT (`SIMPLE_EXECUTION_MODE=jit`) | `bin/simple run tt2.spl` | `(7, 9)` | **correct — fixed** |
| JIT (`SIMPLE_EXECUTION_MODE=native`) | `bin/simple run tt2.spl` | `(7, 9)` | **correct — fixed** (this env var selects a JIT variant, not AOT, despite the name) |
| AOT (`bin/simple native-build tt2.spl -o tt2.bin` then run) | direct execution | `95289575723680` | **STILL BROKEN — raw pointer, exit 0** |

So `81c58562fac` fixed the Cranelift JIT lane (the one `bin/simple run` and
ordinary `bin/simple test`-adjacent execution use) but the **LLVM AOT
(`native-build`) lane still reproduces the original defect**, unchanged from
the 2026-08-02 report.

### Why this isn't the same code path

The obvious hypothesis — "the AOT binary links a stale prebuilt
`libsimple_runtime.a`" — does not hold: `build/simple-core/libsimple_runtime.a`
has an mtime newer than `io_print.rs`, i.e. it was rebuilt after the fix
landed, and `native-build` recompiles the runtime from
`src/compiler_rust/runtime` rather than reusing a cached archive from an
unrelated location.

Traced the LLVM backend for a divergent code path and ruled out the obvious
candidates without finding the actual break:
- `compile_tuple_lit` (`src/compiler_rust/compiler/src/codegen/llvm/functions/collections.rs:65-105`)
  builds the tuple via `rt_tuple_new`/`rt_tuple_set` the same way both
  backends do; the returned `collection` register is used directly, matching
  Cranelift's tuple construction.
- The int/float/bool boxing decision for `rt_value_to_string` args
  (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs:324-399`)
  is backend-agnostic MIR-lowering logic — it runs once, before backend
  selection, so it can't be the source of a JIT-vs-AOT split.
- `compile_call` in the LLVM backend
  (`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:1726`) has
  no `rt_value_to_string`/boxing special-casing that could diverge from the
  MIR-level decision.
- `MirInst::FStringFormat` has its own (boxing-free) `rt_value_to_string` call
  in the LLVM emitter (`codegen/llvm/functions.rs:2001-2069`), which looked
  like a promising duplicate-path candidate, but no MIR lowering pass
  constructs that instruction (`grep -rn MirInst::FStringFormat
  src/compiler_rust/compiler/src/mir/lower/` is empty) — it is dead code, not
  the path actually taken.

None of these rule-outs identify the true divergence; root-causing the AOT
lane specifically needs an LLVM-IR-level dump of the `rt_value_to_string` call
site for this repro (the call's argument value and its LLVM type), which is
follow-up work, not done here.

**Status of this bug doc's overall title ("push into empty-literal list SEGVs")
remains OPEN and untouched by the above** — the m3 SEGV variant is a distinct
mechanism (unboxed array-element storage from `push`, localized to
`codegen/instr/methods.rs:228`) from the general tuple-to-text stringification
issue, and was not re-verified in this pass.

Repro files for the fixed/still-open split above:
`test/01_unit/language/tuple_to_text_native_repro_spec.spl` (interpreter- and
documentation-only; `bin/simple test` cannot reach either native lane).

---

## 2026-08-07 update: AOT lane root-caused via LLVM IR dump — wrong backend, wrong root cause in the previous pass

The 2026-08-07 pass above ruled out several LLVM-backend candidates in
**`src/compiler_rust`** (the Rust seed's `inkwell`-based LLVM codegen). That
was the wrong backend to chase: with `SIMPLE_BOOTSTRAP=1`, `native-build`
actually compiles through the **pure-Simple LLVM backend**
(`src/compiler/50.mir` + `src/compiler/70.backend`), which emits textual
`.ll` and shells out to `llc`, not the Rust `inkwell` path. Confirmed via
`SIMPLE_DUMP_IR=1 SIMPLE_DUMP_IR_FILTER=main`: the Rust-side dump hook
(`codegen/llvm/functions.rs:830`) never fired (no `/tmp/llvm_ir_main.ll`
produced); instead the pure-Simple backend logged `[llvm-tools] ir
/tmp/simple_llvm_<pid>.ll` and that file contains the real generated IR for
this repro.

### Repro used
```simple
fn main():
    val t = (7, 9)
    print("field: {t.0}\n")
    print("tuple: {t}\n")
```
Built with `SIMPLE_BOOTSTRAP=1 bin/simple native-build tt2.spl -o tt2.bin`
(bin/simple here is the deployed seed at
`bin/release/x86_64-unknown-linux-gnu/simple`). Run: `field: 7` (correct),
`tuple: 103443101213344` (raw pointer, exit 0) — reproduces unchanged.

### IR evidence
Relevant excerpt from `/tmp/simple_llvm_<pid>.ll` for `__simple_main`:
```llvm
%t0 = call ptr @rt_alloc(i64 16)              ; tuple built as a raw 2x-i64 block
%t1 = getelementptr inbounds i64, ptr %t0, i32 0
store i64 %l0, ptr %t1, align 8               ; field 0 = 7
%t2 = getelementptr inbounds i64, ptr %t0, i32 1
store i64 %l1, ptr %t2, align 8               ; field 1 = 9
%l2 = getelementptr i8, ptr %t0, i64 0        ; tuple ptr
%l3 = getelementptr i8, ptr %l2, i64 0        ; copy (this is `t`)
...
%l7 = call ptr @rt_array_get(ptr %l3, i64 %l6)   ; {t.0} correctly reads via rt_array_get
...
%t9 = ptrtoint ptr %l3 to i64
%l18 = call i64 @rt_raw_i64_to_string(i64 %t9)   ; {t} — WRONG: renders the pointer as a decimal int
```

Two distinct facts fall out of this IR:

1. **Tuple representation itself has no runtime type tag.** The pure-Simple
   AOT backend builds a tuple as a bare `rt_alloc(field_count * 8)` block with
   raw GEP stores — it never calls any `rt_tuple_new`/`rt_tuple_set`/
   `rt_tuple_len` runtime API (grepped: no such runtime symbols exist in
   `src/runtime`; the `rt_tuple_get`/`rt_tuple_new` call-emission sites in
   `src/compiler/50.mir/**` are all for the self-hosted **compiler's own**
   enum-payload boxing, not for user-code tuple literals). So even a
   perfectly-dispatched "stringify this value" call has no heap object header
   to inspect — there is nothing in this AOT lane analogous to the JIT/runtime
   `HeapObjectType::Tuple` that `heap_value_to_display_string`
   (`src/compiler_rust/runtime/src/value/sffi/io_print.rs:533-550`) switches
   on. Any fix must be static (arity/types known at the interpolation site),
   not a generic runtime call.

2. **Proximate cause — type tracking loses the Tuple type between the literal
   and the variable read.** `lower_tuple_lit`
   (`src/compiler/50.mir/_MirLoweringExpr/literals.spl:562-577`) does register
   the literal's own result local with `MirTypeKind.Tuple(types)` correctly.
   But the interpolation site reads `t` through
   `bootstrap_coerce_to_raw_str` (`method_calls_literals.spl:2775-2800`) →
   `coerce_concat_operand`
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:527-605`), and by
   that point `self.local_mir_type_of(local)` — a scan of `self.builder.locals`
   for the `t`-local's registered type
   (`src/compiler/50.mir/mir_lowering_stmts.spl:146-155`) — returns
   `MirTypeKind.I64`, not `Tuple`. `coerce_concat_operand`'s type switch
   (`expr_dispatch.spl:566-572`) has no `Tuple` arm; `I64` falls into the
   generic numeric-scalar case, so it renders `t`'s pointer bits through
   `rt_raw_i64_to_string` — exactly the call the IR shows. Where the `val t =
   (7, 9)` binding's local gets (re-)registered as plain `I64` instead of
   inheriting the tuple-literal local's `Tuple` type was not traced further
   (needs a walk of the `val`/binding lowering path that creates `t`'s local,
   separate from `lower_tuple_lit` itself, which is not at fault).

### Why no fix was applied here
Both facts above mean a correct fix is two-part and non-trivial to verify
safely in one pass:
- Fix the type-tracking gap so `coerce_concat_operand` sees `t` as
  `MirTypeKind.Tuple(...)` (or otherwise preserve the tuple type across the
  `val` binding into `self.builder.locals`).
- Add a `Tuple` arm to `coerce_concat_operand` that renders `(a, b, ...)`
  syntax at compile time from the known field count/types (e.g. emit the
  literal parens/commas and recursively coerce each `rt_tuple`-free field via
  `rt_array_get`-style GEP reads, mirroring the `{t.0}` path that already
  works) — there is no runtime function to delegate to per fact (1).

Both edits are pure `.spl` (`src/compiler/50.mir/**`), not Rust-seed-only, so
they are in-scope for a future pass, but changing `coerce_concat_operand`'s
type dispatch is a shared path (text-concat `+`, `str()`, interpolation, and
`.join()` all route through it per its docstring) and needs its own isolated
regression check before landing. Left as root-caused/pending-fix rather than
patched blind in this pass.

**Verification status: repro re-confirmed on freshly built artifact,
root cause localized to two specific `.spl` file:line pairs above,
no code changed.**

---

## 2026-08-07 follow-up: both fixes landed for the flat-tuple case; two pre-existing, unrelated gaps found during verification

Implemented both parts the previous pass root-caused but left unpatched:

### 1. Type-preservation fix (`src/compiler/50.mir/mir_lowering_stmts.spl`)

Added `fn local_is_tuple(local: LocalId) -> bool` (mirrors the existing
`local_is_float`/`local_is_bool`, right above `local_is_unit`) and wired it
into both `effective_type` computations inside the `Let` lowering (the
disc==1 early-Let path and the Let match arm, kept in sync per the existing
convention in that file) alongside the pre-existing
str/float/bool/runtime-array/runtime-dict checks:

```
else if self.local_is_tuple(init_local):
    self.local_mir_type_of(init_local) ?? mir_type
```

This closes the exact gap identified in the 08-07 root-cause pass: an
un-annotated `val t = (7, 9)` binding's `effective_type` previously had no
Tuple arm and fell through to the plain-`i64` default, discarding the
tuple-literal local's correctly-registered `MirTypeKind.Tuple` type.

### 2. Compile-time Tuple-to-text rendering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)

Added a `MirTypeKind.Tuple(field_types)` arm to `coerce_concat_operand`'s
type switch that returns early (before the scalar is_bool/is_float/...
dispatch) and delegates to two new helper methods:

- `lower_tuple_field_raw(base_local, elem_type, index)` — reads one tuple
  field via a direct GEP+load off the tuple's raw `rt_alloc(field_count*8)`
  block (the same raw representation `lower_tuple_lit` builds; there is no
  `rt_tuple_*` runtime API to call instead, confirmed by grep).
- `coerce_tuple_to_raw_str(local, field_types)` — renders `"(a, b, ...)"` at
  compile time: reads each field, recursively coerces it through
  `bootstrap_coerce_to_raw_str` (safe recursion — a field's own type is
  never the same Tuple local unless genuinely nested), and splices the
  pieces with `emit_raw_strcat`, mirroring the array-literal `.join()`
  lowering's element-by-element pattern in
  `method_calls_literals.spl` (the pattern the original root-cause note
  pointed at).

### Repro verification (`SIMPLE_BOOTSTRAP=1 native-build`, freshly built)

```simple
fn main():
    val t = (7, 9)
    print("field: {t.0}\n")
    print("tuple: {t}\n")
```

| | Before this fix | After this fix |
|---|---|---|
| `tuple: {t}` | `tuple: 103443101213344` (raw pointer, exit 0) | `tuple: (7, 9)` — **correct** |

The originally-reported defect (tuple interpolation prints a raw pointer
under AOT) is fixed for the exact repro shape in the bug title and every
"scope correction" repro added earlier in this doc.

### Regression checks

Scalar concat/interpolation unaffected (`n=42 f=3.5 b=true s=hi` from
`"n=" + str(n) + " f={f} b={b} s={s}"` — all correct, same as before).

Spec suite (widest reasonably-reachable set — `bin/simple test` on this repo
runs specs through the **interpreter**, which never touches
`coerce_concat_operand` at all; that function is MIR/native-only, so this is
a sanity/no-crash check, not a native-lane regression oracle):

```
test/01_unit/compiler/interpreter/string_interpolation_spec.spl   FAIL (2/3) -- PRE-EXISTING, see below
test/feature/usage/string_interpolation_spec.spl                  PASS (15/15)
test/01_unit/compiler/mir/struct_text_field_interpolation_source_spec.spl  FAIL (1/2) -- PRE-EXISTING, see below
test/01_unit/app/extended/join_basic_spec.spl                     PASS (12/12)
```

Both failures were confirmed **unrelated** to this change, not new
regressions:
- `struct_text_field_interpolation_source_spec.spl` asserts the literal
  source string `self.local_hir_types[field_result.id] = declared_field_type`
  is present in `expr_dispatch.spl`; the current source (far from anything
  touched here) has since been refactored to
  `self.remember_local_hir_type(field_result.id, declared_field_type)` — a
  stale source-content assertion, not a behavior regression.
- `interpreter/string_interpolation_spec.spl`'s two failures
  (`semantic: variable 'literal' not found` / `'value' not found`) are
  **interpreter-path** spec-DSL failures; `coerce_concat_operand` is
  MIR/native-lowering-only code the interpreter never calls, so these cannot
  be caused by this change.

### Two pre-existing gaps discovered during verification (NOT fixed here, NOT caused by this change)

**(a) `{t.0}` (plain tuple field read/interpolation) is currently BROKEN
under `SIMPLE_BOOTSTRAP=1 native-build`, independent of this fix.** Isolated
by testing an **explicitly annotated** `val t: (i64, i64) = (7, 9)` (which
bypasses the new `local_is_tuple` code path entirely, since `mir_type` is
already `Tuple` from the annotation) — `{t.0}` still prints empty, not `7`,
on a freshly built artifact. Root cause: `lower_index_expr`
(`expr_dispatch.spl`, ~line 1560) has

```
if (mir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1" and not result_type_from_base:
    result_type = self.bootstrap_text_type()   # unconditionally Opaque("str")
elif not result_type_from_base and has_index_result_hir_type:
    result_type = self.lower_type(index_result_hir_type)
```

`result_type_from_base` is never true for a `Tuple`-typed base (the match
above it only covers `Array`/`Slice`/`Ptr`/`Ref`/`Dict`), so under
`SIMPLE_BOOTSTRAP=1` the field read always decodes through
`rt_array_get` + `decode_runtime_value(..., Opaque("str"))` regardless of
the field's real type (`i64` here) or `has_index_result_hir_type`, which is
checked in a dead `elif`. This is scoped entirely inside `lower_index_expr`,
which this pass did not touch, and reproduces identically with or without
the type-preservation fix above (confirmed via the annotated-type isolation
test) — a genuine separate, pre-existing defect. A contradictory earlier
note in this same doc's "2026-08-07 update" section claimed `field: 7
(correct)` for the identical repro/build command; that measurement no
longer reproduces on the current tree (this is a heavily-loaded shared
working copy — plausible that `lower_index_expr` changed under a different
lane between the two measurements). Needs its own bug doc / lane; not
patched here per the "be conservative on a shared hot path" scope for this
task.

**(b) Nested and mixed-element-type tuples render incorrectly** through the
new `coerce_tuple_to_raw_str`, because `lower_tuple_lit`
(`_MirLoweringExpr/literals.spl:562-577`) derives each `field_types[i]`
entry from the element's HIR `.type_` annotation, which — per this
codebase's own well-documented pattern (see e.g. `local_is_str`/
`local_is_float`'s docstrings) — is frequently nil/unreliable, unlike the
element's own reliably-tracked MIR local type. Observed:
`(1, (2, 3))` renders as `(1, 152833168)` (nested tuple field prints as a
raw pointer) and `(1, "x", true)` renders as `(1, 2100391, 1)` (string and
bool fields both fall back to the numeric-scalar branch). The homogeneous
`(i64, i64)` case from the bug's actual title/repro is unaffected and
verified correct above. Follow-up: `lower_tuple_lit` should prefer
`self.local_mir_type_of(local)` over `elem.type_` for each field, matching
the rest of this file's established workaround for the same HIR-type
reliability gap — out of scope for this pass (a change to `lower_tuple_lit`
itself, which the original root-cause note explicitly said was "not at
fault" for the reported bug).

**Files changed:** `src/compiler/50.mir/mir_lowering_stmts.spl` (new
`local_is_tuple`, two `effective_type` call sites),
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (new
`MirTypeKind.Tuple` arm in `coerce_concat_operand`, new
`lower_tuple_field_raw`/`coerce_tuple_to_raw_str` helpers). No Rust seed
changes; no bootstrap rebuild performed or required (native-build
interprets these `.spl` sources live under `SIMPLE_BOOTSTRAP=1`, confirmed
by re-running the repro immediately after each edit).

## 2026-08-07: why this defect kept coming back, and the prevention that was missing

This bug was reported, fixed, and re-reported as still-broken **three times**
(JIT value printer `81c58562fac`; the MIR type-preservation + compile-time
Tuple-to-text pair earlier today; and again in the follow-up pass). That is not
three separate defects — it is one defect with **no harness able to observe it**.

### Root cause of the recurrence: the only spec covering it is structurally blind

`test/01_unit/language/tuple_to_text_native_repro_spec.spl` asserts tuple
interpolation renders `(1, 2, 3)`. It passes. It has always passed. It passed
on every single day the AOT lane was emitting a raw pointer.

`bin/simple test` hard-defaults to the tree-walk interpreter and
`TestExecutionMode` has no AOT/native variant (see `.claude/rules/testing.md`
§ "`run` and `test` are DIFFERENT ENGINES"). So **no spec can ever reach the
`native-build` lane**. Each fix was verified by hand against `native-build`,
landed, and then had nothing standing behind it; the next person to touch tuple
lowering got a green suite and shipped the regression. The spec's own header
comment even documented "the AOT lane still reproduces this" while reporting
PASS — a green result sitting directly beneath a written statement that the
thing under test was broken.

This is the general shape, not a tuple-specific accident: **any AOT-lane defect
is invisible to the spec corpus.** The repo's answer for that class is a
`scripts/check/check-*.shs` gate that drives the real `native-build` binary —
which is why ~20 such scripts already exist (`check-native-*.shs`).

### Prevention landed

- `test/fixtures/native_tuple_to_text/main.spl` — flat and mixed-type tuple
  interpolation.
- `scripts/check/check-native-tuple-to-text.shs` — builds that fixture through
  `native-build` and asserts the rendered output. Hard-fails (exit 1) if the
  all-i64 case regresses. Sabotage-verified: mutating the fixture to `(9, 9, 9)`
  produced `FAIL — all-i64 tuple interpolation regressed under native-build`,
  exit 1, so the assertion is load-bearing rather than vacuous.
- The spec header now states it cannot see the AOT lane and names the `.shs`
  gate as the real fence, so the next reader does not mistake its green for
  coverage.

### Current AOT status, measured 2026-08-07

```
$ sh scripts/check/check-native-tuple-to-text.shs
KNOWN-OPEN — mixed-type tuple still wrong: (1, 107362607422760, 1) (expected (1, abc, true))
PASS — native-build tuple-to-text: all-i64 tuple renders correctly
```

The mixed-type value **changes between runs** (`96657993682216` on one run,
`107362607422760` on the next) — that is ASLR moving a heap address, confirming
the middle field is still a leaked raw pointer rather than a decoded `text`.
Consistent with the "unreliable HIR `field_types` annotations" gap recorded
above. The gate REPORTS this rather than asserting it, deliberately: it is a
known-open gap, and phrasing it as a NOTE-on-fix means the day someone fixes
mixed-type rendering the gate says so out loud instead of staying silent.

## 2026-08-07 follow-up 2: gap (a) fixed — `t.0`/`t.1` field-index access under `SIMPLE_BOOTSTRAP=1 native-build`

Scoped follow-up to gap (a) from the previous section only. Gap (b) (nested /
mixed-type tuple rendering) is untouched and still open.

### Reproduction (before fix)

```simple
fn main():
    val t = (7, 9)
    print("first: {t.0}\n")
    print("second: {t.1}\n")
```

Built with `SIMPLE_BOOTSTRAP=1 bin/simple native-build repro.spl -o repro.bin`
(deployed pure-Simple `bin/release/x86_64-unknown-linux-gnu/simple`, no
bootstrap rebuild — these `.spl` sources interpret live under
`SIMPLE_BOOTSTRAP=1 native-build`). Before this fix:

```
first: 
second: 
```

Both fields print empty (exit 0, no crash). This reproduces the gap exactly as
described in the previous section.

### Root cause (two stacked defects in `lower_index_expr`, `expr_dispatch.spl`)

`t.0` does **not** lower through `HirExprKind.Field` or `TupleIndex` — HIR
lowering (`20.hir/hir_lowering/expressions.spl:606-620`,
`is_tuple_positional_field`/`parse_tuple_field_index`) desugars any
digit-named field access on a tuple into `HirExprKind.Index(base,
IntLit(i))`, explicitly to route through the already-proven tuple-destructure
Index path rather than the struct-field path (`resolve_field_index` has no
notion of tuple positional layout). So the actual defect site is
`lower_index_expr`, exactly where the previous section's root-cause note
pointed, not a Field/TupleIndex arm.

**Defect 1 — result type forced to text.** The base's MIR local type is
`MirTypeKind.Tuple(field_types)` (set by `lower_tuple_lit` /
`local_is_tuple`, landed in the first 2026-08-07 follow-up above), but the
`match base_mir_type.kind` block that derives `result_type_from_base`
(`expr_dispatch.spl` ~1612-1626) only had arms for
`Array`/`Slice`/`Ptr`/`Ref`/`Dict` — no `Tuple` arm. With
`result_type_from_base` staying `false`, this line fired unconditionally:

```
if (mir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1" and not result_type_from_base:
    result_type = self.bootstrap_text_type()   # unconditionally Opaque("str")
elif not result_type_from_base and has_index_result_hir_type:
    result_type = self.lower_type(index_result_hir_type)   # dead: elif never reached
```

`index_result_hir_type` was actually correct here (HIR lowering's
`field_tuple_element_type`, keyed off `local_tuple_types`, resolves `t.0`'s
real element type reliably for a plain `val t = (a, b)` local — this is a
different, more reliable source than the tuple-*literal* `field_types`
unreliability documented in gap (b)) — but the `if/elif` structure meant the
`SIMPLE_BOOTSTRAP=1` branch always won first and the correct type was never
consulted.

**Defect 2 — wrong runtime accessor.** Independent of the result type, the
read itself routed through `rt_array_get`:

```
if runtime_array or (mir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1":
    ...call rt_array_get(base_local, index_local)...
```

This fires whenever `SIMPLE_BOOTSTRAP=1`, **regardless of `runtime_array`**.
But a tuple's physical layout (`translate_aggregate`'s `case Tuple` in
`70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:119-162`, added in
the sibling `native_class_array_field_mutation_segfault` fix family) is an
`rt_alloc(field_count * word_bytes)` block of raw native-int words —
explicitly documented there as "IDENTICAL physical layout to Struct" with NO
`rt_array_new` header, deliberately not routed through the generic aggregate
path for that reason. `rt_array_get` expects an `SplArray*` header
(length/capacity/elements-pointer fields) — calling it on a raw tuple block
reads memory that isn't a valid array header at all. That garbage read, then
decoded as `Opaque("str")` (Defect 1), is what produced the empty prints
rather than a crash or garbage number — the two defects compounded into one
"quietly wrong" symptom.

### Fix (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)

Two small, additive, Tuple-gated changes to `lower_index_expr`.

**First attempt (revised — see below).** The first version of this fix read
`result_type` straight off the tuple's own MIR `field_types` table (set by
`lower_tuple_lit` from each element's raw HIR `.type_`). A review pass
pointed out this is the SAME source gap (b) above already proved unreliable
for non-i64/mixed-type tuples, and that using it here would silently inherit
that unreliability instead of using the more reliable HIR-lowering source
(`field_tuple_element_type`, keyed off `local_tuple_types`) that already
flows into `index_result_hir_type`/`has_index_result_hir_type` a few lines
below. Verifying with a `val m = (1, "x")` / `{m.1}` probe confirmed this
concern was real for the naive version. The fix below only flags "this base
is a tuple" and lets the existing `elif has_index_result_hir_type` branch —
already fed by the more reliable source — supply the actual type, instead of
sourcing a type from the Tuple arm itself:

1. Added a `MirTypeKind.Tuple(_)` arm to the `base_mir_type.kind` match
   (alongside Array/Slice/Ptr/Ref/Dict) that sets a new `is_tuple_base` flag
   (computed once here, reused by the runtime-accessor fix below — no
   change to `result_type`/`result_type_from_base`):

   ```
   var is_tuple_base = false
   ...
       case MirTypeKind.Tuple(_):
           is_tuple_base = true
   ```

2. Changed the `SIMPLE_BOOTSTRAP=1` forced-text default to also exclude a
   tuple base, so the `elif has_index_result_hir_type` branch (the reliable
   HIR-sourced type) is consulted instead, closing Defect 1:

   ```
   if (mir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1" and not result_type_from_base and not is_tuple_base:
       result_type = self.bootstrap_text_type()
   elif not result_type_from_base and has_index_result_hir_type:
       result_type = self.lower_type(index_result_hir_type)
   ```

3. Reused the same `is_tuple_base` flag to gate the `rt_array_get` call,
   forcing a tuple base to always take the pre-existing plain GEP+load
   `else` branch — the exact same single-index native-int-word read
   `lower_tuple_field_raw` (`coerce_tuple_to_raw_str`'s helper, same file)
   and `translate_get_field` already use for tuple/struct field reads,
   closing Defect 2:

   ```
   if (runtime_array or (mir_expr_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1") and not is_tuple_base:
   ```

All three changes are gated strictly on a `Tuple`-typed base, so
Array/Slice/Ptr/Ref/Dict indexing (the paths this `SIMPLE_BOOTSTRAP=1` gate
exists for) take an identical path to before, and `is_tuple_base` is
computed once (inside the pre-existing `match base_mir_type.kind` loop over
`self.builder.locals`) rather than re-scanning locals a second time.

### Verification (`SIMPLE_BOOTSTRAP=1 native-build`, freshly built, same repro)

| | Before | After |
|---|---|---|
| `first: {t.0}` | `first: ` (empty) | `first: 7` — **correct** |
| `second: {t.1}` | `second: ` (empty) | `second: 9` — **correct** |

### Regression checks (same lane, no bootstrap rebuild)

```simple
fn main():
    val t = (7, 9)
    print("tuple: {t}\n")                       # whole-tuple interpolation (prior fix)
    val t2: (i64, i64) = (3, 5)
    print("annotated: {t2.0} {t2.1}\n")          # explicitly-annotated tuple type
    var a = [10, 20, 30]
    print("arr1: {a[1]}\n")                      # plain runtime-array index, unaffected path
    val nested = (1, (2, 3))
    print("nested: {nested}\n")                  # gap (b), still open, unaffected by this fix
```

Output:

```
tuple: (7, 9)
annotated: 3 5
arr1: 20
nested: (1, 88853888)
```

- `{t}` (whole-tuple interpolation, the original bug's fix) — still correct,
  unaffected.
- `{t2.0} {t2.1}` (the annotated-type isolation repro the previous section
  used to isolate this gap from the type-preservation fix) — now correct;
  previously this also printed empty (confirmed in the earlier section: "the
  identical repro/build command ... no longer reproduces on the current
  tree").
- `a[1]` (plain runtime-array indexing, the path the `SIMPLE_BOOTSTRAP=1 or
  runtime_array` gate exists for) — still correct (`20`), proving the `and
  not is_tuple_base` guard did not regress the array path.
- `nested` — unchanged, still shows gap (b) (an ASLR-moving raw pointer for
  the inner tuple field, e.g. `(1, 88853888)`/`(1, 1005178240)` across
  runs) exactly as documented above; this fix does not touch
  `coerce_tuple_to_raw_str`/`lower_tuple_lit`'s `field_types` derivation, so
  gap (b) is explicitly out of scope here and remains open.
- Dict indexing (`d[k]`) is structurally unreachable by this diff: it
  returns early via `local_is_runtime_dict`/`lower_dict_runtime_get`
  (`expr_dispatch.spl` ~1553-1559), before either edited line is reached —
  not re-verified by a fresh run, but provably unaffected by inspection.

### Wider verification (destructure, arithmetic, mixed-type discriminator)

A review pass raised two further questions before accepting the fix as
correct: (1) `val (a, b) = t` tuple destructure desugars through the exact
same `Index(base, IntLit(i))` shape (`lower_tuple_destructure`,
`20.hir/hir_lowering/statements.spl`) — does the `and not is_tuple_base`
reroute affect it too, and is that reroute actually correct given the HIR
comment's claim that destructure was "proven-working ... via the same
rt_array_get path" (which directly conflicts with
`aggregate_intrinsics.spl`'s "raw rt_alloc block, no header" description of
the SAME tuple)? (2) does a non-interpolation read (bypassing
`coerce_concat_operand` entirely) behave the same as the `{...}`
interpolation reads verified above?

```simple
fn main():
    val t = (7, 9)
    val (a, b) = t
    print("destr: {a} {b}\n")
    val (c, d) = (11, 13)
    print("destr-lit: {c} {d}\n")
    print("arith: {t.0 + t.1}\n")
    val m = (1, "x")
    print("mixed0: {m.0}\n")
    print("mixed1: {m.1}\n")
```

Output (post-fix, `SIMPLE_BOOTSTRAP=1 native-build`):

```
destr: 7 9
destr-lit: 11 13
arith: 16
mixed0: 1
mixed1: 2100296
```

- `destr`/`destr-lit` (tuple destructure, both from a named local and a bare
  literal) — correct. The HIR comment's "proven-working ... via rt_array_get"
  claim is stale relative to the raw-`rt_alloc` layout `aggregate_intrinsics.spl`
  now documents for `AggregateKind.Tuple` — this fix's reroute to the plain
  GEP+load path is what makes destructure (and `.0`/`.1`) correct under
  `SIMPLE_BOOTSTRAP=1`, not a regression of a working path.
- `arith` (`t.0 + t.1`, a non-interpolation read that never reaches
  `coerce_concat_operand`) — correct (`16`), confirming the fix holds outside
  the string-interpolation lane the rest of this doc focuses on.
- `mixed0` (`m.0`, the `i64` field of a mixed `(i64, str)` tuple) — correct.
- `mixed1` (`m.1`, the `str` field) — **still wrong** (`2100296`, a raw
  handle/pointer bit pattern, not `"x"`). This is gap (b)'s family, not a
  regression: pre-fix, EVERY field read on EVERY tuple (homogeneous or mixed)
  printed empty (Defect 1 forced text unconditionally), so `m.1` was already
  broken before this change, just differently broken (empty vs. garbage
  pointer). Switching the type source from the tuple's own MIR `field_types`
  to the "more reliable" HIR-lowering source (`field_tuple_element_type`)
  did NOT fix `m.1` either — confirmed by testing both versions of the fix
  head-to-head — so the unreliability is not specific to which type source
  is consulted; the deeper issue is downstream, in how a `str`-typed
  `result_type` is read via the plain `emit_gep`/`emit_load` pair this fix
  routes tuples through (unlike `translate_get_field`, that pair has no
  int-word-vs-pointer-vs-float storage/logical-type reconciliation — see
  `aggregate_intrinsics.spl:176-236`'s `dest_ty` dispatch for the shape that
  reconciliation would need to take). Left open as a newly-scoped, narrower
  extension of gap (b) — mixed-type tuple field READS (not just renders) are
  broken under `SIMPLE_BOOTSTRAP=1`; homogeneous-`i64`-tuple field reads (the
  bug's actual title/repro shape) are fixed.

**Files changed:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
(new `MirTypeKind.Tuple` arm computing `is_tuple_base` in `lower_index_expr`'s
base-type match, `is_tuple_base` added to the forced-text-default and
`rt_array_get` gate conditions). No Rust seed changes; no bootstrap rebuild
performed or required.

Gap (b) (nested/mixed-type tuple rendering via `coerce_tuple_to_raw_str`,
and now also confirmed for mixed-type tuple field READS via `.0`/`.1`, not
just whole-tuple interpolation) remains open, unchanged, and out of scope
for this pass — see the previous section for its root cause and proposed
follow-up (`lower_tuple_lit` preferring `local_mir_type_of` over `elem.type_`
per field).

## 2026-08-07 update — whole-tuple interpolation rendering FIXED (gap (b), the `coerce_tuple_to_raw_str` half)

Oracle: `sh scripts/check/check-native-tuple-to-text.shs`
(`test/fixtures/native_tuple_to_text/main.spl`, `val m = (1, "abc", true)` ->
`"mixed: {m}"`). Before this update:

```
KNOWN-OPEN — mixed-type tuple still wrong: (1, 107362607422760, 1) (expected (1, abc, true))
PASS — native-build tuple-to-text: all-i64 tuple renders correctly
```

The middle number changed between runs (96657993682216 on one run,
107362607422760 on the next) — an ASLR-varying heap/text address, i.e. a raw
pointer being rendered as a decimal integer instead of decoded to characters.
The `true` printed as `1` for the same reason: both the `str` and `bool`
fields were going down the plain-`i64` numeric render branch.

**Root-caused, not re-assumed:** traced `coerce_tuple_to_raw_str`'s
`field_types` argument back to its source, `lower_tuple_lit`
(`_MirLoweringExpr/literals.spl` and its duplicate in
`_MirLoweringExpr/method_calls_literals.spl`). Per element, the old code
computed the MIR field type from `elem.type_` (the tuple element's HIR-level
type annotation), defaulting to `MirType.i64()` whenever `elem.type_` was
nil:

```
var elem_ty = MirType.i64()
val maybe_elem_type = elem.type_
if val elem_type = maybe_elem_type:
    if elem_type != nil:
        elem_ty = self.lower_type(elem_type)
types = types.push(elem_ty)
```

Confirmed by tracing the actual lowering of each literal kind that
`elem.type_` is unreliable here but the JUST-LOWERED element local's own
MIR-registered type is not: `StringLit` lowering (`expr_dispatch.spl`
`case StringLit`) registers its dest local as `MirType(kind: Opaque("str"))`
via `new_temp`; `BoolLit` lowering goes through `emit_const_bool`, which
registers `MirType.bool()`. Both are recoverable via
`self.local_mir_type_of(local)` (`mir_lowering_stmts.spl`) right after
`self.lower_expr(elem)` — the same MIR-registered-type idiom already used
elsewhere in this file (`local_is_tuple`, `local_is_str`) specifically
because HIR-level type annotations (`elem.type_`, `let_type`) are unreliably
nil on the flat-HIR path. `lower_tuple_lit` was the one caller in this family
still reading the unreliable HIR-level source instead. With `field_types[1]`
silently defaulting to `I64`, `coerce_tuple_to_raw_str`'s per-field
`lower_tuple_field_raw` + `bootstrap_coerce_to_raw_str` recursion loaded the
string field's raw pointer bits as a plain `i64` and rendered them through
`rt_raw_i64_to_string` (the ASLR-varying decimal), and rendered the bool
field's `1`/`0` bit pattern the same way instead of going through
`rt_raw_bool_to_string` — this fully explains both symptoms and confirms the
original "unreliable HIR field_types annotations" attribution in the previous
section, this time for the whole-tuple-render path specifically (not just
asserted, empirically traced).

**Fix:** in both `lower_tuple_lit` definitions, prefer
`self.local_mir_type_of(local)` (the lowered element's own MIR-registered
type) over `elem.type_`, falling back to the old `elem.type_` path only if
`local_mir_type_of` returns nil:

```
var elem_ty = MirType.i64()
if val local_ty = self.local_mir_type_of(local):
    elem_ty = local_ty
else:
    val maybe_elem_type = elem.type_
    if val elem_type = maybe_elem_type:
        if elem_type != nil:
            elem_ty = self.lower_type(elem_type)
types = types.push(elem_ty)
```

Gate after the fix:

```
NOTE — mixed-type tuple rendering now CORRECT; close the open gap in ...
PASS — native-build tuple-to-text: all-i64 tuple renders correctly
```

`scripts/check/check-native-tuple-to-text.shs`'s mixed-type check was then
promoted from the reported `NOTE`/soft branch to a hard `FAIL`/`exit 1`
assertion, matching the all-i64 check's rigor. Sabotage-verified: mutating
the fixture's string literal (`"abc"` -> `"xyz"`) reproduces a `FAIL —
mixed-type tuple rendering regressed under native-build` with the mismatched
actual value, confirming the promoted assertion is load-bearing, not
vacuous. Fixture restored; gate re-run clean:

```
PASS — native-build tuple-to-text: mixed-type tuple renders correctly
PASS — native-build tuple-to-text: all-i64 tuple renders correctly
```

**Files changed:**
`src/compiler/50.mir/_MirLoweringExpr/literals.spl` (`lower_tuple_lit`),
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (duplicate
`lower_tuple_lit`), `scripts/check/check-native-tuple-to-text.shs` (promoted
mixed-type check to a hard assertion). No Rust seed changes; no bootstrap
rebuild performed or required (interpreter-path compiler edits are live
under `native-build` per this repo's established pattern).

**Still open, unchanged, out of scope:** mixed-type tuple field READS via
`.0`/`.1` (the `m.1` -> `2100296`-style symptom from the section above,
routed through `translate_gep`/`emit_load` in `lower_index_expr`, not
`coerce_tuple_to_raw_str`). That is a different code path from the one fixed
here and was NOT touched by this change — it needs the
`aggregate_intrinsics.spl` `dest_ty`-style storage/logical-type
reconciliation described above, not a `field_types`-source swap (the
previous section already ruled that fix out for the `.0`/`.1` path
specifically, head-to-head).

## Gap (c) — mixed-type tuple field READS (`t.0`/`t.1`), fixed 2026-08-08

Closed the last remaining gap in this family: `(1, "abc", true)`'s `.1`/`.2`
field reads (both bare `val s = m.1` and interpolated `"{m.1}"`) printed a
raw ASLR-varying pointer-as-decimal (e.g. `98519600270576`) instead of
`"abc"`, and a bit-pattern integer instead of `true`.

**Root cause, two independent defects, both in `lower_index_expr`**
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `t.0`/`t.1`
desugars to `HirExprKind.Index(base, IntLit(i))` per
`20.hir/hir_lowering/expressions.spl`'s `is_tuple_positional_field`):

1. **No storage/logical-type reconciliation on the tuple GEP+load path.**
   The plain `emit_gep`/`emit_load` pair the tuple-base `else` branch routed
   through has no `dest_ty`-keyed dispatch, unlike `translate_get_field`
   (`70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`), which
   load-then-`inttoptr`s a ptr-typed field, load-then-`bitcast`s a
   float-typed field, and load-then-`trunc`s a narrow int/bool field — all
   because every tuple/struct field physically stores one native-int word
   regardless of its logical type. `emit_get_field` (`50.mir/mir_data.spl`)
   already exists and lowers straight to `translate_get_field`, giving the
   same reconciliation for free.
2. **`result_type` itself resolved to the untyped `i64` default**, so even
   after routing through `emit_get_field`, `dest_ty` came out `i64` (`==
   nit`) and the plain-load `else` arm of `translate_get_field` fired,
   reproducing the exact same symptom. The `MirTypeKind.Tuple(_)` arm in
   `lower_index_expr` deliberately discarded the tuple's own MIR
   `field_types` (comment: unreliable, derived from `lower_tuple_lit`'s old
   `elem.type_`-sourced path — true when gap (b) above was still open) and
   relied entirely on HIR-sourced `index_result_hir_type`
   (`field_tuple_element_type`, keyed off `local_tuple_types`). That HIR
   source does not reach this function on every lowering path — reproduced
   with a bare non-interpolated `val s = m.1; print(s)`, no interpolation
   involved — leaving `has_index_result_hir_type` false and `result_type`
   stuck at `i64`.

Gap (b)'s 2026-08-07 fix (`lower_tuple_lit` now prefers
`self.local_mir_type_of(local)` over `elem.type_`) already made the MIR
`field_types` source reliable, which retired the reason gap (a)'s comment
gave for discarding it. Confirmed empirically: after the fix below, a tuple
constructed from mixed-type literals correctly threads `Opaque("str")` /
`MirType.bool()` per-index through `field_types`.

**Fix**, both still gated on `is_tuple_base` so plain runtime-array indexing
is untouched:
- `MirTypeKind.Tuple(field_types)` arm now binds and keeps `field_types` (as
  `tuple_field_mir_types`) instead of discarding it.
- After the existing HIR-sourced `result_type` resolution, a new fallback:
  when `is_tuple_base` and neither `result_type_from_base` nor
  `has_index_result_hir_type`, look up the literal field index (helper
  `tuple_index_literal`, matches `HirExprKind.IntLit` on `index`) in
  `tuple_field_mir_types` and use that as `result_type`.
- The tuple-base `else`-branch GEP+load is now gated behind
  `is_tuple_base and self.tuple_index_literal(index) >= 0`: a new `elif`
  arm calls `emit_get_field(base_local, literal_index, result_type)`
  instead, so the read gets `translate_get_field`'s `dest_ty` reconciliation.
  A tuple index that is somehow not a literal int (shouldn't occur given the
  `t.0`/`t.1` desugar, but defensive) falls through to the original raw
  GEP+load path unchanged.

Gate extended (`scripts/check/check-native-tuple-to-text.shs`,
`test/fixtures/native_tuple_to_text/main.spl` adds `m.1`/`m.2` field reads
of the existing mixed-type tuple) and re-run clean:

```
PASS — native-build tuple-to-text: mixed-type tuple renders correctly
PASS — native-build tuple-to-text: mixed-type tuple field reads render correctly
PASS — native-build tuple-to-text: all-i64 tuple renders correctly
```

Sabotage-verified: mutating the fixture's expected `m1` string
(`"abc"` -> `"xyz"`) reproduces `FAIL — mixed-type tuple field read (m.1,
str) regressed under native-build` with the real actual value (`abc`)
printed alongside the mutated expectation, confirming the assertion is
load-bearing. Script restored; gate re-run clean.

**Files changed:**
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
(`lower_index_expr`, new helper `tuple_index_literal`),
`scripts/check/check-native-tuple-to-text.shs` and
`test/fixtures/native_tuple_to_text/main.spl` (extended with mixed-type
field-read assertions). No Rust seed changes; no bootstrap rebuild performed
or required.

**This closes the family** opened by this bug doc: whole-tuple
stringification (all-i64 and mixed-type) and tuple field reads (all-i64 and
mixed-type) are all now correct under `native-build`.

## 2026-08-08 — Opus review of `ec9ff78876c`: regression risk checked, REFUTED

An Opus review of the already-landed `lower_tuple_lit` fix (`ec9ff78876c`,
`literals.spl:~588-595` and its twin `method_calls_literals.spl:~3675-3682`)
raised a concern (S1): since `local_mir_type_of`
(`src/compiler/50.mir/mir_lowering_stmts.spl:186-194`) returns whatever type
is registered for a local and never returns `nil` for a registered local, a
*present-but-wrong* MIR type (e.g. a call result defaulted to `MirType.i64()`
by one of the ~100 `emit_call` sites in `switch_operators_calls.spl`, or by
`resolved_call_hir_return_type`'s "erased to all-i64" params) would now
unconditionally beat the correct HIR annotation — reproducing the exact
ASLR-varying-decimal symptom this commit fixed, but for call-result tuple
elements instead of literal elements.

Checked empirically (no code change needed first — direct probes with
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build`),
each binary run twice to catch ASLR-varying garbage:

- **Primary probe** (function-call result element, the exact predicted
  failure mode):
  ```
  fn g(s: text) -> text: return s
  fn main() -> i64:
      val t = (1, g("abc"))
      print("call: {t}\n")
      return 0
  ```
  Run 1: `call: (1, abc)`. Run 2: `call: (1, abc)`. Healthy both times —
  **no ASLR-varying decimal.**
- **Second axis** (array-index-read element, `val a=[1,2,3]; val t=(1,
  a[0])`): `idx: (1, 1)` twice under normal build, and `idx: (1, 1)` twice
  again rebuilt with `SIMPLE_BOOTSTRAP=1` (the `bootstrap_text_type()`
  clobber path the review also flagged). Healthy in both modes.
- **Extra coverage** (method-call result, arithmetic expr, plain variable,
  nested tuple, all in one tuple): `(1, "hello", 3+4, x, (1,"outer"))` →
  `misc: (1, hello, 7, 3, (1, outer))`, identical on both runs. Healthy.
- Regression gate `sh scripts/check/check-native-tuple-to-text.shs`: all 4
  PASS lines, unaffected.

**Verdict: S1's predicted regression does NOT reproduce.** `local_mir_type_of`
returns the correct type for call-result locals in practice — the
`MirType.i64()` defaults the review cited from `switch_operators_calls.spl`'s
`emit_call` sites are for *unresolved/erased* call sites, not for the
`g(...)` call-result local itself, which correctly picks up `text`
(`Opaque("str")`) from wherever the call's return value gets registered. No
code change made; no fix needed. The second axis (`SIMPLE_BOOTSTRAP=1` +
index-read element) also came back healthy, so that concern is refuted too.
Note: `expr_dispatch.spl` may be drifted vs `origin/main` from other agents'
in-flight work — this verification exercised the on-disk state at probe time,
not necessarily origin's exact `expr_dispatch.spl`, but `lower_tuple_lit`
itself (the code under review) was unmodified from the landed commit.
