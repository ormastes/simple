# V9 IM + Zicsr + Zifencei system-test plan

## Requirement matrix

| Requirement | Structural scenario | Clocked full-pipeline GHDL scenario |
| --- | --- | --- |
| REQ-G2-012 | exactly 21 children; exactly one tag-2 and one tag-3 owner; 12 fault sources | independent held results, ready isolation, reset, exact-once retirement |
| REQ-G2-013 | exact RV32/RV64 V9 plans and every M row; V7/V8/noncanonical rejection | all MUL/DIV/REM rows, special cases, RV64 W 32-bit geometry/sign extension |
| REQ-G2-016 | six CSR rows, class 6/effect 3/tag 3, frozen service ABI | six forms, x0, absent/privilege/read-only traps, frozen lookup and exact-once commit |
| REQ-G2-017 | V9 composition retains the typed FENCE owner and explicit Zifencei profile gate; standalone owner/cycle scenarios are the direct evidence | standalone FENCE/FENCE.I effect-acknowledgement and backpressure scenarios; V9 full-pipeline integration remains pending |
| NFR-G2-003 | repeat strict lowering receipt/VHDL equality for RV32 and RV64 | generated entity compiles and runs in GHDL; formal/RVFI readiness retained |

## Required artifacts

- `test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_class_router_v9_spec.spl`
- `test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_pipeline_v9_flat_spec.spl`
- `test/01_unit/compiler/backend/riscv_scalar_runtime_pipeline_v9_flat_to_vhdl_spec.spl`
- `test/02_integration/compiler/riscv_scalar_runtime_pipeline_v9_flat_clocked_ghdl_spec.spl`
- `test/01_unit/compiler/backend/riscv_scalar_runtime_pipeline_v9_rvfi_to_vhdl_spec.spl`
- versioned V9 RVFI prove, cover, and mutation job artifacts plus receipt reducer
- `doc/08_tracking/bug/riscv_scalar_runtime_v9_formal_rvfi_receipt_gap_2026-08-13.md`
- `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v9_im_zicsr_spec.spl`
- mirrored manual `doc/06_spec/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v9_im_zicsr_spec.md`

The system scenario uses `step("Construct the canonical V9 RV64 pipeline")`,
`step("Offer a tag-2 M operation")`, `step("Offer a tag-3 CSR operation")`,
and `step("Retire the held completion once")`. Reusable setup is `@inline`;
the generated manual keeps primary flows visible and executable machinery
folded. Each `it` has concrete built-in-matcher assertions, no placeholders.

## Clocked vectors and negatives

Run both XLENs. Tag 2 covers MUL/MULH/MULHSU/MULHU; RV64 additionally covers
MULW, DIVW, DIVUW, REMW, REMUW. Both widths cover DIV/DIVU/REM/REMU, signed
negative values, divisor zero, signed min/-1, x0 sources/destination, hostile
RV64 W upper bits, backpressure, consume, reset, and malformed canonical row,
raw binding, width, identity, event, lineage, and illegal-marker requests.

Tag 3 covers CSRRW/CSRRS/CSRRC/CSRRWI/CSRRSI/CSRRCI, source/destination x0,
read-only write, missing CSR, privilege/reserved policy, no-policy-failure
commit, lookup-data mutation after accept, commit stability while stalled, and
one commit only when the held completion consumes. The mixed sequence proves a
held tag-2 result does not create CSR effects and a held tag-3 result does not
alter M arithmetic/ready state. Inject each of the 12 fault sources once and
prove gated input, completion, LSU/fence, and CSR service effects.

## Acceptance

First run source structural/unit lanes with the admitted pure-Simple runtime;
then run the full pipeline GHDL lane once; then run the required formal/RVFI
prove, cover, and mutation jobs for the V9 wrapper. The legacy
`check-riscv-formal-dual-track.shs` is not V9 proof evidence. A
Rust bootstrap seed, isolated provider-only GHDL test, or manually edited
manual is not acceptance evidence. Generate the mirrored manual with
`spipe-docgen` and require zero stubs before verification.

For each exact V9 profile, generate the sealed formal bundle with the admitted
release runtime, then pass that directory unchanged to the runner:

```sh
bin/release/<triple>/simple run src/app/verify/riscv_scalar_runtime_pipeline_v9_formal_bundle.spl -- \
  build/v9-formal/v9_rvfi32 v9_rvfi32 rv32im_zicsr_zifencei
sh scripts/rtl/run-riscv-scalar-runtime-pipeline-v9-formal.shs \
  build/v9-formal/v9_rvfi32 v9_rvfi32 rv32im_zicsr_zifencei
```

Repeat with `v9_rvfi64` and `rv64im_zicsr_zifencei`. The runner alone may
replace the pending manifest with the profile/input/tool-bound receipt consumed
by the strict reducer.
