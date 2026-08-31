# An array literal's Aggregate instruction is absent from the emitted LLVM module

- **Filed:** 2026-08-31
- **Status:** OPEN — isolated to a 6-line repro, five hypotheses refuted by measurement
- **Blocks:** Stage-2 admission (`bootstrap_stage2_struct_receiver`, positional arm), therefore Stages 3/4/5
- **Platform:** aarch64-apple-darwin. **NOT shown to be macOS-specific** — nothing in the
  mechanism is platform-dependent; it has simply not been reproduced elsewhere yet.

## Symptom

`llc` rejects the emitted module:

```
error: use of undefined value '%l5'
  %l6 = getelementptr i8, ptr %l5, i64 0  ; copy
```

The `; copy` for the Let is emitted and reads the array literal's LocalId, but
**no `call ptr @rt_array_new` appears anywhere in the function**. The defining
Aggregate instruction is missing while its destination id is in use.

## Minimal repro (6 lines, no imports)

```
fn agg_empty(path: text) -> text:
    var parts: [text] = []
    parts.push(path)
    parts.join("/")

fn main():
    print(agg_empty("a/b"))
```

`simple native-build --backend llvm` on the Stage-2 candidate → `llc` failure above.
Runs in seconds; no bootstrap needed to reproduce once a candidate binary exists.

## Refuted by direct measurement — do not re-propose

1. **Empty-literal special case.** `var parts: [text] = ["seed"]` fails identically
   (`%l5` undefined). Elements lower fine — `rt_string_new` is emitted — so
   emptiness is not the discriminator. The split is aggregate-typed vs scalar Lets.
2. **Backend `translate_aggregate`.** Its `Array` arm emits `rt_array_new`
   unconditionally, including for zero operands
   (`_MirToLlvm/aggregate_intrinsics.spl:95`).
3. **MIR optimisation passes (DCE / copy-prop).** `native-build --list-optimizations`
   reports these as *inventory-only*; `dce.spl` unconditionally returns true.
4. **Backend dispatch silently dropping it.** The terminal catch-all eprints
   `E-BACKEND-LLVM-INST-Unknown`; failing runs emit **zero** such lines. An added
   explicit discriminant fast path for `Aggregate` (mirroring the existing
   `Const`/`Copy`/`GlobalAddr` ones) produced **byte-identical IR** — reverted.
5. **`MirBuilder` value-semantics aliasing.** `MirBuilder` IS a struct and
   `lower_array_lit` DOES call `self.builder.emit_aggregate(...)` in place while the
   neighbouring `lower_dict_lit` uses the `var b = self.builder … self.builder = b`
   write-back idiom — a convincing fit. Applying the write-back to both
   `lower_array_lit` copies changed nothing: `rt_array_new` calls still 0, `llc`
   error byte-identical. Reverted. **Fitting the file's conventions is not evidence.**

## Independent of the SSA LocalId defect (measured)

Fixed separately in `a32bccaf866a`: three arms passed a `LocalId?` unwrapped, packing
`MirInstKind.Call`'s variant index (24) into the high word, giving ids of the form
`(24<<32)+n`. That fix is verified — corrupted ids went **132/182 → 0** on the repro
fixture — and the `llc` error remained **byte-identical**. So these are two defects,
not one; the single-cause account that predicted otherwise is refuted.

## Where to look next

The Aggregate is created (`emit_aggregate`, `mir_data.spl:702`, does `new_temp` +
`emit`) and the backend arm exists (`core_codegen.spl:823`), yet the instruction is
absent from the emitted module while its id survives into the Copy. The gap is
between MIR construction and backend dispatch. Untested so far: whether the
instruction is present in the MIR *block* actually handed to the backend (no MIR dump
facility exists — `SIMPLE_MIR_DUMP`/`dump_mir` find nothing), and whether the block it
is emitted into is the block that gets flushed.

**Note on probes:** `SIMPLE_BOOTSTRAP_DEBUG=1` produced zero `[mir-to-llvm]` lines on
this path — `bootstrap_debug_enabled()` is gated on `allow_ambient_codegen_policy`
(`_MirToLlvm/class_def.spl:133`), so absence of those prints is NOT evidence about
control flow. A probe that cannot fire proves nothing.

## Methodology note

Five vacuous runs were caught during this investigation, each of which would have read
as a fix: a 180s gate timeout (`status 124`) reporting 0 errors; a fixture swept
because `build/` is gitignored (`lines=4`); a non-executable binary (`rc=126`); an
`--opt-level 0` run whose flag does not exist, shifting arg parsing into a whole-tree
build; and `corrupted_ids=0` on a fixture that never had corrupted ids. **Every run
must be checked for non-vacuity (line count, rc, and an actual artifact) before its
number is read as a result.**

## Isolation narrowed 2026-08-31 (all measured on the Stage-2 candidate)

| case | result |
|---|---|
| `["a", "b"].join("/")` — literal used DIRECTLY as a receiver | **BUILDS**, binary produced (and needs no `rt_array_new`) |
| `var parts = ["a", "b"]` — bound to a local, NO annotation | fails, `use of undefined value` |
| `var parts: [text] = ["a", "b"]` — bound to a local, annotated | fails, byte-identical |
| `var parts: [text] = []` — empty, annotated | fails, byte-identical |

Two conclusions:

1. **The type annotation is NOT the trigger** — annotated and unannotated fail
   identically. The earlier framing ("declared aggregate annotation") is wrong.
2. **The split is BOUND-TO-A-LOCAL vs USED-DIRECTLY.** An array literal consumed
   in place lowers and links fine; the same literal bound to a local loses its
   Aggregate. That moves the search decisively into the Let handler, and off
   `lower_array_lit`, which is common to both paths.

## Prime remaining suspect: the Let handler's stale builder snapshot

`mir_lowering_stmts.spl` takes `var b2 = self.builder` at :1206, calls
`b2.emit_copy(local, init_local)` at :1228, and writes back `self.builder = b2`
at :1260. `MirBuilder` is a STRUCT (`mir_data.spl:113`) with value semantics, so
**any instruction emitted into `self.builder` between :1206 and :1260 is silently
discarded by that write-back**. This is the same aliasing hazard the file works
around elsewhere, applied over a much wider window than the idiom intends.
NOT yet confirmed: it must be shown that the Aggregate (or a re-emission of it)
actually lands inside that window.

## The two defects are separable, and now separately diagnosable

`var t = (1, 2)` — a TUPLE bound to a local — does not produce the undefined-value
error at all. It raises the new `E-MIR-TYPE-ZeroKind` instead, i.e. the *other*
defect (a well-formed HirType whose `kind` is raw 0). So:

- array literal bound to a local -> Aggregate absent (this bug)
- tuple literal bound to a local -> ZeroKind (the type-layer bug)

The `E-MIR-TYPE-ZeroKind` diagnostic added in `a32bccaf866a` is what makes these
two distinguishable at a glance; previously both surfaced as the same opaque
`disc=-1: 0`.
