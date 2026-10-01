# V8 combined Zmmul + Zicsr agent handoff

## Product boundary

Merge owner: primary Codex.  Final reviewer: normal/highest-capability model.
The delivered source lane is the V8 flattened product for exactly
`rv32i_zmmul_zicsr_zifencei` and `rv64i_zmmul_zicsr_zifencei`: existing Zmmul
tag-two service plus the class-6/tag-three dynamic CSR owner.  It excludes
IM and all DIV/REM behavior.

## Completed lanes

| Lane | Owner | Artifact boundary |
| --- | --- | --- |
| Combined decoder/profile and routing | Primary | V8 pipeline and class router; exact class 6/effect 3/tag 3 |
| CSR admission/capture/commit | Primary | Plan-bound one-entry provider, held completion, policy trap/no commit, exact-once commit |
| Fault and backend | Primary | V8 global fault gate and strict VHDL renderer |
| Structural traceability | Primary | System spec/manual for REQ-G2-013, REQ-G2-016, NFR-G2-003 |
| Lower-model sidecars | N/A | No remaining delegated code lane; any future broad review is advisory only |

## Review invariants

- Capture CSR presence/read value and final intent only on accepted request;
  never consult live service data while a completion is held.
- Malformed tag-three metadata is a sticky protocol fault; absent/privilege/
  read-only policy is an execute trap with no CSR commit.
- x0 source is zero; rd x0 affects writeback only.
- Commit occurs with the held completion's single consume edge only.
- Do not widen profiles to IM or add a separate DIV/REM owner.

## Remaining owner task: qualification

**BLOCKED:** an admitted self-hosted Simple binary and GHDL are required.
After deployment at `bin/release/x86_64-unknown-linux-gnu/simple`, the merge
owner runs:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/compiler/riscv_scalar_runtime_pipeline_v8_flat_clocked_ghdl_spec.spl --mode=interpreter
```

The final reviewer may accept the V8 implementation only after both admitted
lanes have successful evidence.  Until then, this handoff records no PASS and
authorizes neither release nor profile expansion.
