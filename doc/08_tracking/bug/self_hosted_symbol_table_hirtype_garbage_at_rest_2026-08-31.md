# Self-hosted Stage-2 reads a garbage `HirType` from the symbol table — three reader fixes were all treating a symptom

- **Filed:** 2026-08-31
- **Status:** OPEN — root cause localised, not fixed
- **Blocks:** Stage-2 admission (`bootstrap_stage2_positional_stage3_route`), therefore Stages 3/4/5
- **Platform:** aarch64-apple-darwin. NOT shown to be macOS-specific.

## Symptom

The Stage-2 struct-receiver gate's positional arm fails with, repeatedly:

```
error: bootstrap MIR lowering: E-MIR-TYPE-Unknown: unreachable HirTypeKind
       disc=-1: 0 while lowering 'compiler.common.module_path_naming.*'
```

No crash — `rc=1`, clean and attributed. Arm 1
(`bootstrap_stage2_struct_receiver`) PASSES.

## Localisation

Every `lower_type` call site in `mir_lowering_stmts.spl` was labelled with a
module-scalar id, printed at the error site. Result was unambiguous:

```
8 occurrences, ALL site=1
```

Site 1 is the Let handler's read of the binding's declared type, originally
`self.symbols.get_symbol_type_raw(symbol_value_id)`.

## The decisive measurement

Discriminant probed immediately before and after the unwrap at that site:

```
2 runs   pre=-1            post=1984125491 / 3031551406
2 runs   pre=3031551406    post=3031551406
```

**`pre` is already garbage.** Note also that 3031551406 is not a plausible
`HirTypeKind` discriminant (the enum has on the order of tens of variants), so
the "pre valid" rows are garbage too — `-1` and a 3-billion value are just two
renderings of the same corruption.

The value is therefore corrupt BEFORE any unwrap, i.e. as it comes out of the
symbol table.

## What this refutes

Three reader-side fixes were landed against this defect on this branch. **All
three were treating a symptom** and none can have addressed the cause:

| attempt | commit | result |
|---|---|---|
| `case Some` -> `.?`/`.unwrap()` | 6d3856e6b4b | E-MIR-TYPE 20->0 **on the seed**; unrelated to the self-hosted path |
| `.unwrap()` -> `??` | 0f2bc5e6e34 | removed a SIGSEGV (real), did not touch disc=-1 |
| typed rebinds + de-box | c0bc07223ee | measured inert, A/B N=10 each |

A fourth attempt — rerouting the call site through `get_symbol_raw` so the
`HirType?` never crosses a method boundary — also measured **identical** and was
reverted rather than landed.

## Why the boundary hypothesis was attractive, and why it is not sufficient

`hir_symbol_table_methods.spl:485-491`, on the SIBLING accessor
`get_symbol_named_type_raw`, states:

> This keeps both `HirType?` and `SymbolId?` inside SymbolTable; neither
> value-type optional is safe across the staged-native method boundary used by
> nested field lowering.

`get_symbol_type_raw` returns exactly a `HirType?` across that boundary, so it
violates a constraint its own neighbour documents. That remains a real latent
defect worth fixing on its own merits. It is NOT the cause here: routing around
it changed nothing, measured.

## Where the defect must be

Between the HIR writer storing `HirSymbol.type_` and the MIR reader observing it,
in the SELF-HOSTED binary only. The Rust seed does not reproduce it: with the
seed, the same source measured E-MIR-TYPE = 0 across N=10. So this is a
stage-2-codegen defect in how a `HirType` aggregate is stored in or retrieved
from the symbol table, not a logic error in either endpoint.

## Measurement protocol note — READ THIS BEFORE CHASING COUNTS

The disc=-1 COUNT is bimodal and heap-layout dependent. Ten runs of ONE unchanged
binary produced 22 (x4), 8 (x3) and 4 (x3). A sequence of single-run counts
across builds is NOT a progress signal, and was twice misread as one on this
branch. Any claim about this defect needs per-run TMPDIR, N>=10, and COUNTS
reported rather than sequences.

## Reproduce

```sh
C=<stage2 binary>   # the lane deletes it on rejection; capture it as it is linked
RTD=build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority
sh scripts/check/check-bootstrap-stage2-struct-receiver.shs "$C" "$RTD" \
   aarch64-apple-darwin cranelift
# arm 1 PASS; positional arm rc=1 with E-MIR-TYPE-Unknown disc=-1
```
