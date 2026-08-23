# Five MIR backends converted from silent fail-open to named assert

- **Landed:** 2026-08-23
- **Status:** DONE for the conversion; **expect fallout** — see "Expected fallout" below
- **Policy:** "add assert or todo; disable what is not completed optional" (user, 2026-08-23)
- **Map:** `doc/09_report/mir_construct_coverage_matrix_2026-08-23.md`
- **Gate:** `scripts/check/check-mir-backend-failclosed.shs`
- **Sibling:** `check-codegen-unlowered-mir-fails-build.shs` (LLVM + C, made loud first)
- **Precursor record:** `mir_constructs_silently_dropped_by_fail_open_backends_2026-08-23.md`

## What was wrong

25 `MirInstKind` constructs were dropped by ALL FIVE of these backends while the
build reported success — including `Drop`, the WP-E affine `resource` release
edge, which simply never happened.

## Correction to the precursor record's wording

That record said all five "emit nothing and no diagnostic". Verified per site,
that is exactly true of **two** of them; the other three left an inert artifact.
All five are fail-open — the build succeeds with the instruction absent — but the
distinction matters and is recorded rather than smoothed over:

| site | behaviour BEFORE | truly silent? |
|---|---|---|
| `cranelift_codegen_adapter.spl:761` | `case _: ()` | **yes** |
| `common/mir_text_codegen.spl:180` -> `translate_unsupported` (L289) | empty method body `()` | **yes** |
| `llvm_lib_translate_expr.spl:225` | `print "warning: unhandled MIR instruction kind (skipped)"` | no — unnamed warning, continues |
| `wasm/wat_codegen.spl:393` | `builder.emit(";; unhandled instruction")` | no — inert WAT comment |
| `opencl_backend.spl:346` | `"// unsupported MIR instruction for OpenCL subset"` | no — inert C comment |

The three non-silent ones named neither the construct nor, usefully, the
backend, so they were not actionable; a WAT/C comment has no runtime effect at
all. My census reported the *dispatch* line and the brief reported the *sink*
line for two of these — both are correct, they are different points on the same
path.

## What changed

Each site now ASSERTS with a named, greppable code following the existing C and
LLVM shape (`E-BACKEND-<NAME>-INST-<Variant>` + `panic`, with the same
`SIMPLE_ALLOW_UNLOWERED_MIR=1` escape hatch):

- `E-BACKEND-CRANELIFT-INST-<Variant>`
- `E-BACKEND-MIRTEXT-INST-<Variant>` — the shared base trait, widest blast radius
- `E-BACKEND-LLVMLIB-INST-<Variant>`
- `E-BACKEND-WASM-INST-<Variant>`
- `E-BACKEND-OPENCL-INST-<Variant>`

**Nothing was deleted.** No construct, arm, or test was removed. The two
text backends that must return a value (`wasm`, `opencl`) additionally emit a
`TODO(unlowered-mir)` marker on the escape-hatch path, so the "explicitly
disabled" state is visible in the generated artifact instead of being a bare
skip — the "todo" half of the policy.

New shared table `src/compiler/70.backend/backend/common/mir_inst_variant_name.spl`
maps `MirInstKind` -> variant name for all 126 variants, generated from the
registry and **verified arm-by-arm against `mir_instruction_kinds.spl`
(126/126 present, 0 arity mismatches)**. It exists so five backends do not
hand-maintain five copies of the same name list.

## Expected fallout — report it, do not suppress it

This turns currently-green builds red **wherever these constructs are reachable**.
That is the point: those builds were emitting code with instructions missing.
A failure surfacing here is a pre-existing defect becoming visible, not a
regression introduced by this change.

The 25 constructs dropped by all five are the likeliest triggers:
`Drop`, `TransferIn`, `TransferOut`, `FreezeRegion`, `AcquireSnapshot`,
`CommitUpdates`, `ResultMatchSemantic`, `HostGpuLaneBegin`, `HostGpuLaneEnd`,
and 16 SIMD/warp/predicated constructs.

`SIMPLE_ALLOW_UNLOWERED_MIR=1` restores the previous behaviour for a lane that
must keep moving while a real fix is prepared. It is an escape hatch, not a
fix, and it is the same one C and LLVM already use.

## Deliberately NOT touched

`MirType.size_bytes()` / the aggregate store-stride reconciliation
(`mir_type_simd_vector_size_bytes_returns_8_2026-08-23.md`,
`mir_codegen_aggregate_slot_size_vs_store_stride_disagree_2026-08-23.md`). Those
two defects currently CANCEL for single-field aggregates and must be fixed as a
pair, in their own commit. No sizing code is modified here.

## Evidence

```
$ sh scripts/check/check-mir-backend-failclosed.shs --selftest
PASS — 5 selftest fixture(s) checked, 0 fail-open
$ sh scripts/check/check-mir-backend-failclosed.shs
PASS — 5 site(s) and 126 variant(s) checked, 0 fail-open
```

Neuter-verified against real source (restored and re-verified PASS/exit 0 after each):

```
# A: restore opencl's silent catch-all
fail-open site(s): opencl(no E-BACKEND-OPENCL-INST diagnostic);
FAIL — 5 site(s) and 126 variant(s) checked, 1 fail-open     # exit 1

# B: delete one arm from the shared name table
variant(s) with no arm in the shared name table: Drop
FAIL — 5 site(s) and 126 variant(s) checked                  # exit 1
```

`bin/simple lint`: **0 errors** on the new 126-arm table and on the edited
OpenCL backend (the linter's REQC004 rationale form is used on the table's
residual arm).
