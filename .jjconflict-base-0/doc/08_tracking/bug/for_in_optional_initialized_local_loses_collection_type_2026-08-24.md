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

## 2026-08-24 (later) — hot-path validation, and what it does and does not cover

The `effective_type` change above is on a hot path and was landed on seven
fixtures plus a site count. That is not proportionate coverage, so it was
validated properly afterwards. Results, including the part that came out
negative.

### There is no test suite for this code path, and that is not a footnote

`simple test` cannot exercise this change **at all**. The pure-Simple test runner
never native-builds: `grep -rnE "native_build|native-build|compile_to_native"
src/app/test_runner_new/` returns nothing, and specs run interpreted.
`effective_type` lives in `50.mir/mir_lowering_stmts.spl`, reached only from
`lower_to_mir`. So a green suite run would have been theatre — it would have
executed zero lines of the change. Stated plainly rather than left as "not
verified".

### Differential native-build corpus: 16 real programs, before vs after

Two `git worktree` checkouts isolating exactly this commit (`9ca094b44ee~1` vs
`9ca094b44ee`), same seed, per-tree `SIMPLE_CACHE_SCOPE`. Corpus chosen by weighting
`test/**` single-file programs toward `Dict<`, `.keys()`, `.values()` and
optional usage.

| | before | after |
|---|---|---|
| build 0 / run 0 | 6 | 6 |
| build 1 (pre-existing failures) | 10 | 10 |

`diff` of the full result files, including each failure's error signature, is
**empty — byte-identical**.

**And that evidence is weaker than it looks, which is the point of reporting it.**
Instrumenting the two new branches with a counter and re-running the same 16
programs gives **TOTAL_NEWBRANCH_HITS=0**. The corpus never entered the changed
code. Byte-identical results therefore establish only that the change does not
perturb paths it does not touch — real, but not evidence that the change itself
is correct.

### Purpose-built corpus that DOES enter the branch

Three fixtures, each confirmed to fire a new branch exactly once:

| fixture | shape | before | after | hits |
|---|---|---|---|---|
| `c1` | `val map: Dict<text,i64> = <fn -> any?>`, `for k in map.keys()` | build FAILS | builds, runs, `n=6` | 1 |
| `c2` | `val xs: [i64] = <fn -> any?>`, `for v in xs` | build FAILS | builds, runs, `s=12` | 1 |
| `c3` | `val xs: [text] = <fn -> any?>`, `for v in xs` | build FAILS | builds, runs, `s=5` | 1 |

`c3` is the element-type check: `v.len()` on a destructured `text` element
returns 2+3=5, which is impossible if the elements had decayed to i64 handles.

### Why the change's blast radius is narrow

The new branches fire only when the annotation is a container AND the
initializer is NOT that same container kind. When the initializer already is one,
the pre-existing arms still handle it unchanged — verified by the two fixtures
that specifically cover them: an annotated dict plus an EMPTY `Dict<text,S>`
literal (Bug #189's shape, `n=5 m=0 elen=0`) and an annotated `[i64]` literal
(`s=6`), both with zero new-branch hits. In well-typed source the only remaining
way to reach the new branches is an Option-wrapped initializer, which is exactly
the defect being fixed; every other combination (annotation `[T]` with a dict
initializer, annotation `Dict` with a float initializer, ...) is already a type
error in the source.

### The remaining 15 are NOT the shape that was just fixed

Earlier framing implied the 12 unannotated `NamedVar` residuals were mechanical
follow-ups. **They are not, and they must not be annotated on that assumption.**
Their actual source shapes, reduced to minimal fixtures, **build and run fine**:

| source shape | site | minimal fixture |
|---|---|---|
| `val lines = check_output.split(NL)` then `for line in lines` | `main_lazy_diag_tools.spl:122` and 5 others | builds, runs (`n=6`) |
| same, with an explicit `[text]` annotation | — | builds, runs (`n=6`) |
| `for ch in name` over a `text` | `main_static_tools.spl:321` | builds, runs (`n=3`) |

None involves an optional initializer, and none reproduces in isolation, so the
cause is contextual and **uncharacterized**. Annotating them would be a guess
dressed as type information — the failure mode worth avoiding, since a wrong
annotation is a lie the compiler will act on. Left alone.

Breakdown of the 15: **12** unannotated `NamedVar`/`I64` (above, uncharacterized),
**2** `Field`/`I64` (`main_lazy_assistant.spl:20`, the field-receiver hole
`fb7e76c489a` left open), **1** `NamedVar`/`Tuple` (not localized — empty span).

### The defect vs the compensation — read this before "15 remaining"

The general hole is the defect and it is **still open**: `val x = f()` with no
annotation, where `f` returns `T?`, still loses `T`, because unwrapping the
Option yields `any` rather than a container. The compiler change fixes only the
case where an annotation EXISTS; the `src/lib/common/json/**` annotations are
**compensation for the open hole**, not a fix for it. Anyone reading "32 -> 15"
as progress toward #143 should read it as "17 sites compensated, one type-loss
class closed, the inference hole untouched".

### Still not verified

- No suite exists for this path (above). The evidence is the 16-program
  differential plus 12 targeted fixtures, nothing broader.
- The 12 residual sites are uncharacterized.
- MCP still produces no binary. Clearing #143 entirely would not be enough:
  `borrow_check()` runs after `lower_to_mir`, so the NLL false positive in
  `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` is still queued
  behind it and has never executed on this closure.

## 2026-08-25 — the hole's ROOT is in the PARSER, and closing it does NOT clear the 12

The general hole named above — `val x = f()` unannotated, `f -> T?`, loses `T` —
is real, is now fixed for every DECLARED payload, and **does not account for the
remaining MCP blockers**. Both halves matter; the second is the one that stops a
wrong conclusion.

### It is not an unwrap problem. `T?` never carried `T` in the first place.

The working hypothesis was that unwrapping an optional yields `any` instead of
the payload. That is not what happens. Probing the HIR signature pass on
`fn optarr(x: i64) -> [i64]?` printed:

```
[reg] fn=optarr parser_kind=TypeKind::Named((Option, []))     <- ZERO type arguments
      ret_lowered=HirTypeKind::Optional(HirTypeKind::Any)
```

The payload is gone at the **parser**, before HIR runs at all.
`parser_absorb_optional_suffix` (`10.frontend/core/parser.spl:522`) absorbed the
`?` tokens and then returned the bare, argless `TYPE_OPTION` **unconditionally,
discarding its `base` argument** — for every `T`, not just containers. The four
`Option<i64|f64|text|bool>` spellings survived only because the explicit
`Option<T>` branch hands in a dedicated tag; the `T?` suffix form lost
everything.

### Fix, in three parts

1. **Parser (the root).** `parser_absorb_optional_suffix` now preserves the
   payload: dedicated tags for `i64`/`f64`/`text`/`bool`, the existing
   `TYPE_OPTION_GENERIC` registry (dedup'd by inner tag, already used for a
   *named* inner) for everything else, and the old bare `TYPE_OPTION` as the
   fallback when the registry is full or the base is already an option tag. It
   can only ever preserve MORE than before, never less. `-> [i64]?` now parses to
   `Named("Option", [Array(i64)])` and lowers to `Optional(Array(Int(64,true)))`.

2. **`Infer` is not an annotation.** `val x = f()` does **not** arrive with a nil
   annotation — it arrives as `Some(Type(kind: TypeKind.Infer))`. A bare
   `type_.?` test therefore reads "annotated" for every inferred binding, which
   is why the first two attempts at the consumer never fired. Added
   `parser_type_kind_is_infer` beside its `parser_type_kind_*` siblings and both
   `val` arms now treat `Infer` as unannotated — the principle MIR already
   records as Bug #138 ("a non-nil-but-Infer-defaulted `type_` is as unreliable
   as a nil one"), made available to HIR.

3. **Payload adoption.** A by-NAME registry `fn_optional_container_returns`,
   populated in the same signature pass and for the same reason as
   `fn_tuple_returns`, is consumed by both `val` arms: no annotation + an
   initializer calling a container-behind-optional function => the binding adopts
   the payload type.

**Part 1 is fully general; part 3 is deliberately container-only.** Adopting the
payload as the binding's type for EVERY optional return would change what `.?`
and `unwrap()` see on hundreds of bindings, and there is no test lane that
native-builds, so no suite would catch a regression. Containers are where the
loss is fatal rather than merely imprecise. Recorded rather than silently scoped.

### Verified

| fixture | before | after |
|---|---|---|
| `fn optarr() -> [i64]?`, `val xs = optarr(1)`, `for v in xs` | build FAILS (#143) | builds, runs, `s=12` |
| `fn optdict() -> Dict<text,i64>?`, `val m = ...`, `for k in m.keys()` | build FAILS | builds, runs, `n=6` |
| `fn optany() -> any?` | build FAILS | build FAILS — **correct** |

The third is not a residual defect: `any?`'s payload genuinely IS `any`, which is
not a container, so there is nothing to recover. A compiler that "fixed" it would
be inventing a type.

### It does NOT clear the remaining 12, and that answers the open question

The natural hypothesis was that the 12 uncharacterized `NamedVar` residuals were
this defect all along. **They are not.** With the fix in place, on
`native-build src/app/mcp/main.spl`:

```
infer-hit count = 0        # the payload-adoption path never fires in the MCP closure
#143 sites     = unchanged
```

Zero, because `json_to_object` and `json_to_array` are declared `-> any?`
(`src/lib/common/json/types.spl:251,267`). Their payload is `any`. There is no
container type in the signature to preserve, so preserving it perfectly changes
nothing. That is also why the hand-written `Dict<text, any>` / `[any]`
annotations recorded earlier remain the right compensation: they supply
information the signature genuinely does not carry.

**The cause of the 12 therefore remains uncharacterized**, exactly as it was.
They are not this defect, and they are not the `split()`/text-iteration shapes
either (those reduce to fixtures that build and run). Whoever picks them up
starts from an open question, not from this fix.

### NOT verified

- Still no test lane that native-builds, so the evidence is a 16-program
  differential plus 9 fixtures — nothing broader.
- Part 1 changes the type TAG for every `T?` in the tree from a single shared
  `TYPE_OPTION` to distinct per-payload tags. Anything comparing option type tags
  for equality would see a behaviour change. Nothing in the corpus did, but the
  corpus is 16 programs.
- MCP still produces no binary. Clearing #143 entirely would still not be enough:
  `borrow_check()` runs after `lower_to_mir`, so the NLL false positive in
  `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` remains queued
  behind it and has never executed on this closure.
