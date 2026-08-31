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
