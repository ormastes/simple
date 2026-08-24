# `for-in` over a local initialized from an OPTIONAL-returning function loses its collection type (#143 residue) (2026-08-24)

- **Status:** OPEN — not fixed. Root cause isolated to a 12-line reproducer.
- **Severity:** HIGH — it is 30 of the 32 remaining `#143` blockers on
  `native-build src/app/mcp/main.spl`
- **Area:** HIR local-type resolution (`20.hir`), surfacing at
  `50.mir/mir_lowering_stmts.spl:2768`
- **Found by:** measuring what the `#143` diagnostic actually covers on a real
  workload, after
  `io_runtime_import_breaks_native_build_len_on_i64_2026-08-24.md` cleared four
  earlier blockers

## The question this answers

`fb7e76c489a` types `Dict<K,V>.keys()`/`.values()` as `[K]`/`[V]` so those loops
stop being "non-array iterables". It was verified `GATE-OPEN` in isolation but
never run against a workload. The obvious hypothesis was that it would clear
some or all of the 32 `#143` sites blocking the MCP build.

**It does not, and it was already present when those 32 were counted** —
`fb7e76c489a` is an ancestor of the tree the count was taken on. The fix is also
**not** at fault: it works. Measured directly, all of these build (rc=0), link,
and RUN with the correct answer:

| fixture | receiver | result |
|---|---|---|
| `val map: Dict<text, i64> = {...}` | dict literal | builds, runs, `typed=2` |
| `val map: Dict<text, any> = {...}` | dict literal | builds, runs, `any=2` |
| `val map: Dict<text, i64> = make()` | same-module call returning `Dict` | builds, runs, `call=2` |
| `val map: Dict<text, i64> = to_obj_dict(x)` | CROSS-module call returning `Dict` | builds, runs, `xmod=2` |
| `val map: Dict<text, any> = to_obj_any(x)` | call returning bare `any` | builds, runs, `any_ret=2` |

## What actually breaks it: an OPTIONAL initializer

The declared type on the `val` is discarded when the initializer's type is
OPTIONAL. Two fixtures differing ONLY in the `?`:

```
fn to_obj_any(value: any) -> any:          # NO question mark
    val d: Dict<text, i64> = {"a": 1, "b": 2}
    d
fn count_x(obj: any) -> i64:
    val map: Dict<text, any> = to_obj_any(obj)
    var n = 0
    for k in map.keys():
        n = n + k.len()
    n
```
-> **builds and runs**, `any_ret=2`.

```
fn to_obj_opt(value: any) -> any?:         # question mark
    ...
fn count_x(obj: any) -> i64:
    val map: Dict<text, i64> = to_obj_opt(obj)
    ...
    for k in map.keys():
```
-> **`for-in over non-array iterables is not supported by native codegen yet
(#143)`**, rc=1, no binary.

Cross-module makes no difference (a cross-module `-> Dict` initializer passes; a
same-module `-> any?` initializer fails), and the annotation's value type makes
no difference (`Dict<text, any>` and `Dict<text, i64>` both fail). **The `?` is
the whole difference.**

A probe at the `#143` site shows why the sibling fix cannot help: the method call
never resolves at all.

```
[i143] itertype=I64 elem=I64 iter=HirExprKind::MethodCall(
    (... NamedVar((SymbolId(id: 4), map)), type_: nil, has_type_: false),
    keys, [], MethodResolution::Unresolved)
```

`MethodResolution::Unresolved` — the receiver's type is unknown, so `keys` is
never recognised as a dict method in the first place. `fb7e76c489a`'s symbol-table
route reads the SYMBOL's type, and for an optional-initialized local that type is
not the annotation.

## Measured breakdown of all 32 MCP blockers

Probe on `50.mir/mir_lowering_stmts.spl:2768`, printing the collection's MIR
type and the iterable's HIR kind:

| count | iterable kind | MIR type | what it is |
|---|---|---|---|
| 12 | `NamedVar` | `I64` | `val list = json_to_array(arr)` etc. — optional initializer |
| 10 | `NamedVar` | `Tuple` | same shape, different erased representation |
| 8 | `MethodCall` | `I64` | `for k in map.keys()`, `val map: Dict<text, any> = json_to_object(obj)` |
| 2 | `Field` | `I64` | `session.<field>` at `src/app/mcp/main_lazy_assistant.spl:20` |

`json_to_object` and `json_to_array` are both declared `-> any?`
(`src/std/common/json/types.spl:251,267`), so **30 of 32 are one root cause**:
the optional-initializer type loss above. The remaining **2** are the
field-receiver hole `fb7e76c489a` explicitly left open — so in practice that hole
costs 2 of 32 here, not the bulk.

The 8 `MethodCall` sites are one source location
(`src/std/common/json/object_ops.spl:88,143,200,202,223,244,265,287` reached
through a single `line: 14` receiver span) monomorphized into 8 instances.

## Spans

All 32 have USELESS spans: the 22 `NamedVar` sites report nothing at all, and the
10 that do report a file give the RECEIVER's span, not the loop's. A sibling lane
saw empty spans on this path and concluded they were normal; on the blocking
sites they mean `#143` cannot be localized from its own diagnostic without
instrumenting the compiler. Worth fixing alongside `#143` — it cost a probe run
to learn something the error should have printed.

## NOT verified

- No fix was attempted. Where the annotation is dropped for an optional
  initializer (the `val` lowering, or `symbols.define`'s stored type) was not
  located.
- Whether repairing this would clear all 30 — they share a symptom and a
  reproducer, but only the 8 `MethodCall` sites were traced to
  `MethodResolution::Unresolved` specifically. The 22 `NamedVar` sites were
  classified by their initializer's declared return type, not by re-running each.
- The 2 `Field` sites are unaffected by any of this and need the struct-field
  type lookup `fb7e76c489a` describes.
- Clearing `#143` does NOT unblock the MCP build on its own. `borrow_check()`
  runs after `lower_to_mir`, so the NLL false positive in
  `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` is queued
  behind it and has never yet executed on this closure.

## 2026-08-24 (later) — FIXED in part, and my attribution above was WRONG

**Correction first, because it is the important part.** The section above says
"the declared annotation is discarded when the initializer's type is optional"
and then attributes **30 of 32** MCP blockers to it. The first half is true and
is now proven at the instruction level. **The attribution is false.** The 30
sites do not carry an annotation at all:

```
src/lib/common/json/object_ops.spl:83   val map = json_to_object(obj)      # no annotation
src/lib/common/json/array_ops.spl:32    val list = json_to_array(arr)      # no annotation
```

Only **3** bindings in `object_ops.spl` (lines 26, 66, 310) were annotated
`Dict<text, any>`, and those three are not the ones the failing `for-in` loops
read. So the annotation-discard defect, fixed on its own, clears **0 of 32**. I
read "the file has annotated bindings of this shape" off the wrong lines and did
not check the ones the loops actually use.

### What the mechanism actually is (measured, both sides of a one-character pair)

The `[let]` probe printed from the running compiler, for
`val map: Dict<text, any> = f(obj)`:

| `f`'s return | init MIR type | `is_tuple` | effective type |
|---|---|---|---|
| `-> any` | `I64` | false | `Dict(Tuple,I64)` — annotation kept |
| `-> any?` | **`Tuple`** | **true** | **`Tuple`** — annotation discarded |

**An OPTIONAL is represented as `Tuple` in MIR.** In
`50.mir/mir_lowering_stmts.spl`, the early-`Let` `effective_type` chain prefers
the initializer's inferred type for array/str/float/bool/**tuple** initializers,
so an optional-returning initializer's `Tuple` beat the explicit `Dict`
annotation. The chain already contained exactly the right guard — "when an
explicit `Dict<K,V>` annotation is present, prefer it" (Bug #189) — but it lived
INSIDE the `local_is_runtime_dict` arm, so it could only fire when the
initializer was already a dict, i.e. never in the case that needed it.

Downstream that is fatal rather than imprecise: `local_is_runtime_dict` tests the
MIR local's type, so a `Tuple`-typed binding is not a dict, `receiver_is_dict`
stays false, `.keys()` never reaches `rt_dict_keys`, and the `for-in` sees a
non-array iterable — reported as "#143 not supported yet", a feature-gap message
for what is actually a lost type. That is why `MethodResolution::Unresolved`
appeared in the earlier probe.

### The fix

Hoist the annotation preference to the FRONT of the chain so it applies for every
initializer kind, and generalise it from `Dict` to containers:

```
else if let_type != nil and annotated_is_dict_pre  and not self.local_is_runtime_dict(init_local):  mir_type
else if let_type != nil and annotated_is_array_pre and not self.local_is_runtime_array(init_local): mir_type
```

Deliberately NOT keyed on `keys`/`values`, on `Dict` alone, or on the initializer
being optional — the rule is "an explicit container annotation outranks the
initializer's inferred type", which is the same principle Bug #189 already
recorded, applied where it was unreachable.

### The other half: the library was missing real type information

With the compiler fixed, the 30 unannotated sites still fail, because there is no
annotation to prefer and the payload type is `any`. Those bindings were annotated
to match what **three sibling functions in the same file already do**:

```
val map: Dict<text, any> = json_to_object(obj)     # 9 sites + 2 map1/map2
val list: [any] = json_to_array(arr)               # 18 sites
```

This is not routing around the compiler: the annotation is genuine type
information the callers omitted, the file's own prevailing style already carries
it, and **without the compiler fix adding it would have changed nothing** — it
would have been discarded exactly as the three existing ones were.

### Measured result

`native-build src/app/mcp/main.spl`, `[i143]` probe count at
`mir_lowering_stmts.spl`:

| state | sites |
|---|---|
| before | **32** |
| compiler fix alone | 32 (fires on 3 bindings; none feed a failing loop) |
| + `Dict` annotations | 24 (all 8 `MethodCall` `.keys()` sites cleared) |
| + array rule + `[any]` annotations | **15** |

Remaining 15: 12 `NamedVar`/`I64`, 2 `Field`/`I64`
(`src/app/mcp/main_lazy_assistant.spl:20` — the field-receiver hole
`fb7e76c489a` left open), 1 `NamedVar`/`Tuple`. The 12 are unannotated locals
(`name`, `lines`, `nested`, ...) in other modules; their spans are empty so they
were not localized.

### Verified

Seven fixtures build, link and RUN with correct output on a clean worktree with a
fresh `SIMPLE_CACHE_SCOPE`: the one-character pair (`pass=2` / `fail=2`, the
latter previously failing); an annotated dict literal plus an EMPTY
`Dict<text, S>` literal (Bug #189's shape — `n=5 m=0 elen=0`); a dict plus a
plain `[i64]` array loop (`n=1 s=6`); and the three fixtures from earlier in this
chain (`v=10`, `s=hello n=7 len=5`, `x=a z=c k=3 zlen=1`), so nothing regressed.

### NOT verified

- **No test-suite run.** Verification is these seven fixtures plus the MCP site
  count. The `effective_type` chain is a hot path and a broad behaviour change to
  it deserves the suite; that was not run.
- The general hole is NOT closed: `val x = f()` with no annotation, where `f`
  returns `T?`, still loses `T`. Unwrapping the Option here yields `any`, which
  is not a container either, so those 12 need real inference or source
  annotations.
- MCP still does not produce a binary, and clearing #143 entirely would not be
  enough on its own: `borrow_check()` runs after `lower_to_mir`, so the NLL false
  positive is still queued behind it and has never executed on this closure.
