# 25 MIR constructs are silently dropped by every fail-open backend

- **Filed:** 2026-08-23
- **Status:** OPEN — not repaired here (a sibling lane owns the fail-open sites)
- **Severity:** CRITICAL for the ownership/resource subset; HIGH for the SIMD subset
- **Found by:** MIR construct-matrix lane
- **Map:** `doc/09_report/mir_construct_coverage_matrix_2026-08-23.md`
- **Gate:** `scripts/check/check-mir-backend-coverage.shs`

## Summary

`MirInstKind` has **126** variants. Five backend dispatch sites terminate their
`match inst_kind:` in a `case _:` that emits **nothing and produces no
diagnostic**. A construct outside such a backend's handled set is *deleted* from
the generated code. The program still compiles, still runs, and returns a wrong
answer.

| backend | source | `case _:` | handled | dropped |
|---|---|---|---|---|
| cranelift | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | L761 | 20/126 | 106 |
| mir text base trait | `src/compiler/70.backend/backend/common/mir_text_codegen.spl` | L180 | 83/126 | 43 |
| llvm lib | `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` | L225 | 27/126 | 99 |
| wasm wat | `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | L393 | 21/126 | 105 |
| opencl | `src/compiler/70.backend/backend/opencl_backend.spl` | L177 | 77/126 | 49 |

`common/mir_text_codegen.spl` is the **shared base trait** every non-overriding
text backend inherits, so its 43 dropped constructs propagate to each of them.

## The 25 dropped by ALL FIVE

No text/JIT backend lowers these at all.

**Ownership / resource (CRITICAL — silent wrong value or silent leak):**
`Drop`, `TransferIn`, `TransferOut`, `FreezeRegion`, `AcquireSnapshot`,
`CommitUpdates`, `ResultMatchSemantic`

- `Drop` is the WP-E affine `resource` drop edge. WP-E's entire contribution is
  computing exactly-once placement of that edge in the CFG; every backend above
  discards it, so the release never happens.
- `AcquireSnapshot` / `CommitUpdates` dropped means reads observe live data and
  writes are discarded — a silent wrong value, not a fault.
- `FreezeRegion` dropped means mutation of a frozen region is no longer prevented.

**Host/GPU lane boundaries (HIGH):** `HostGpuLaneBegin`, `HostGpuLaneEnd`

**SIMD / warp / predicated vector (HIGH) — no scalar fallback is emitted, so the
operation vanishes:** `MaskFromCmp`, `MaskedAdd`, `MaskedFma`, `MaskedMul`,
`MirSimdPermute`, `MirSimdScalableVsetvl`, `MirSimdShuffle`,
`MirWarpActivesMask`, `MirWarpBallot`, `MirWarpReduce`, `MirWarpShfl`,
`MirWarpSync`, `PredicatedAdd`, `PredicatedFma`, `PredicatedMul`,
`ScalableVecFence`

## Structural root cause

`spec/compiler_schema/transitions/` models **five** MIR consumers —
`mir_inst_to_{c_backend,llvm,interp,native_isel}` — and lane C7 (2026-08-21)
converted exactly those to named, spanned `E-BACKEND-*-INST-<Variant>` errors.
The five backends above are modelled by **no transition table at all**. Nothing
can ratchet a consumer that is not in the contract surface, which is precisely
why these five stayed silent while the modelled five were repaired.

There is no `mir_inst_to_cranelift`, `mir_inst_to_wasm`, `mir_inst_to_opencl`,
`mir_inst_to_llvm_lib`, or `mir_inst_to_mir_text`.

## Reproduce

```sh
sh scripts/check/check-mir-backend-coverage.shs   # PASS: 749 pairs, ratchets the current state
```
The guard pins today's handled sets so no backend may silently shrink, and fails
if a new `MirInstKind` variant is added that no backend lowers. It deliberately
does **not** convert any `case _:` into a hard failure — that is a behaviour
change on the JIT path and needs its own commit.

## Fix direction (not done here)

1. Add transition tables for the five unmodelled backends.
2. Replace each `case _: ()` with a named, spanned `E-BACKEND-<NAME>-INST-<Variant>`,
   following the C7 pattern already used by `_MirToLlvm/core_codegen.spl`.
3. For the SIMD/warp subset, either emit a scalar fallback or raise — never drop.
