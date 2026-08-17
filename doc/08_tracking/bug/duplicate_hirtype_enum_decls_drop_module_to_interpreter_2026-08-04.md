# 26 duplicate `enum HirType` declarations collide with the canonical struct, dropping a whole module to the interpreter

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
repro (`SIMPLE_TIMEOUT_SECONDS=0 timeout 200 bin/simple test`) now shows 0
`irrefutable BINDING` lines; the single `[jit-fallback]` at startup is a
DIFFERENT defect in the same duplicate-name family — see
`duplicate_struct_decls_shadow_field_types_2026-08-10.md` (struct field-type
shadowing, partially fixed there). The 26 duplicate `enum HirType` decls still
exist and remain a latent hazard; the guidance below (make the diagnostic name
the winning declaration) still applies if this resurfaces.
**Found:** 2026-08-04, while taking a fresh full-suite baseline.
**Impact:** suite-wide. The compiler itself reports
`whole module dropped to the interpreter (expect ~100-1000x slowdown)`.

## Symptom

A full `bin/simple test` run emits exactly one such line during startup:

```
[jit-fallback] HIR lowering error: Unsupported feature: `case Str:` is not a
variant of the matched enum, so it is an irrefutable BINDING that matches every
remaining value and makes every later arm (including `case _:`) unreachable.
Use a qualified variant (`case Enum.Str:`), or a lowercase name if a binding was
really intended.: whole module dropped to the interpreter (expect ~100-1000x
slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
```

Because it is an *irrefutable binding*, every later arm — including `case _:` —
is unreachable. So the affected `match` does not merely run slowly, it returns
the **first arm's value for every input**. Both the slowdown and the wrong
answer are silent; the run still exits 0.

## Root cause (what is proven)

`HirType` is declared **27 times** with mutually incompatible shapes:

- canonical: `struct HirType` — `src/compiler/20.hir/hir_types.spl:648`
  (its variants live on a separate `enum HirTypeKind`, `hir_types.spl:654`,
  which *does* have a `Str` variant).
- 26 further `enum HirType:` declarations, all under `src/compiler/30.types/`
  plus `src/compiler/25.traits/trait_method_resolution.spl`.

The 26 enum copies do not agree on their variant sets. Five of them have **no
`Str` variant at all** and spell the text type `Text` instead:

```
src/compiler/30.types/bidir_phase1a.spl
src/compiler/30.types/bidir_phase1b.spl
src/compiler/30.types/bidir_phase1c.spl
src/compiler/30.types/bidir_phase1d.spl
src/compiler/30.types/bidirectional_types.spl      # Unit Int Float Bool Text Function Tuple Array Var
```

while the others do (`const_key_type.spl`, `variance_types.spl`,
`macro_def.spl`, `higher_rank_poly_types.spl`, …). There are 42 `case Str:`
sites across 31 files in `src/compiler/`. When such a site resolves against one
of the five no-`Str` declarations, `Str` is not a variant, so it is accepted as
an irrefutable binding and the enclosing module is dropped to the interpreter.

This is the same class of defect already recorded for the symbol registry:
declaration reachability is not import reachability — the five `bidir_*` modules
are imported by **nothing** (their only `use` sites, in
`test/01_unit/compiler/type_inference/bidir_type_check_spec.spl:10` and its two
duplicates, are commented out) and still register `HirType` globally.

## Repro

The fallback does **not** reproduce on small selections
(`test/01_unit/lib/async_core_spec.spl`,
`test/01_unit/compiler/type_inference/bidir_type_check_spec.spl`,
`bidir_check_spec.spl` all report `fallback=0`). It needs the full-suite
co-compilation, but it fires during startup, so a time-boxed run is enough:

```bash
SIMPLE_TIMEOUT_SECONDS=0 timeout 180 bin/simple test > /tmp/tb.log 2>&1
grep -ac 'jit-fallback' /tmp/tb.log      # => 1
```

`SIMPLE_TIMEOUT_SECONDS=0` is required — the `kill_simple_monitor` daemon kills
any run older than 60s, and the killed run never reaches the fallback.

## REFUTED hypothesis: it is not the five no-`Str` declarations

The obvious hypothesis was that a `case Str:` site resolves against one of the
five `bidir_*` declarations that lack a `Str` variant. **This was tested and is
false.** Renaming all five (`HirType` -> `BidirType`, 152 purely local
references, zero importers, `residual HirType=0` verified) and re-running the
identical time-boxed command gave:

| source | `jit-fallback` count | log bytes |
|--------|----------------------|-----------|
| baseline        | 1 | 167917 |
| five renamed    | 1 | 167917 |

Byte-identical output. The rename was reverted; it is not in the tree.

So the losing `case Str:` resolves against one of the **other 21** `enum
HirType` declarations, or against the canonical `struct HirType` itself (a
struct has no variants at all, which would make *every* bare `case X:` against
it an irrefutable binding — the most likely remaining explanation, and it would
mean the 42 sites are matching on a value typed as the struct rather than as
`HirTypeKind`).

## Next step for whoever picks this up

Do not guess again — make the compiler name the declaration. The message is
emitted without file/line; adding the matched type's declaration site to that
diagnostic is the cheapest way to close this, and it pays for itself the next
time this class of bug appears.

## Fix direction

Give the compiler a way to name which declaration a `case` resolved against,
then either (a) make a bare `case Name:` that matches no variant of the
*statically known* enum a hard error rather than a silent binding, or (b)
de-duplicate `HirType` so exactly one declaration is registered. (a) is the
smaller change and turns every remaining instance of this class into a visible
failure instead of a silent wrong answer; `SIMPLE_JIT_STRICT=1` already does
this for the JIT path only.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN but MUCH SMALLER than filed; cited file is a STALE-REF

The cited `src/compiler/20.hir/hir_lowering/types.spl` contains ZERO occurrences
of `enum HirType` (`grep -c` = 0). The declarations live elsewhere, and the count
is now **7 files, not 26**:

```
$ grep -rln "enum HirType" src/compiler/ --include=*.spl | wc -l
7
# incl. src/compiler/20.hir/hir_types.spl (canonical),
#       src/compiler/30.types/higher_rank_poly_types.spl,
#       src/compiler/30.types/const_key_type.spl,
#       src/compiler/50.mir/__init__.spl
```

Re-scope this row to those 7 sites and re-derive which shadow the canonical
struct. Owner paths: src/compiler/20.hir/**, 30.types, 50.mir.
