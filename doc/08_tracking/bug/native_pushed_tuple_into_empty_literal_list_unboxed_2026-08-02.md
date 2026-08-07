# Native lane: a tuple pushed into an empty-literal-initialized list is stored unboxed; any `.N` read SEGVs

- **ID:** native_pushed_tuple_into_empty_literal_list_unboxed_2026-08-02
- **Date:** 2026-08-02
- **Status:** OPEN — root-cause *localized*, not fixed (fix is in Rust seed codegen; seed rebuild was out of scope for the lane that found it)
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
