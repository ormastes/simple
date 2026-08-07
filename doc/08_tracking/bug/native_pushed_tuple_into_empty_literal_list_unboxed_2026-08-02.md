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
