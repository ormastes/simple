# RISC-V Gen2 V9 flattened IM plus Zicsr runtime pipeline

Status: development structural evidence. V9 is exactly `rv32im_zicsr_zifencei` and `rv64im_zicsr_zifencei`: base-I, full-M, Zicsr, and Zifencei. It owns one flat tag-two M provider and one flat tag-three CSR provider in an ordered 21-child direct graph.

Qualification is **BLOCKED**: no admitted pure-Simple self-hosted runtime is available for this exact scenario. The V9 clocked GHDL contract exists at `test/02_integration/compiler/riscv_scalar_runtime_pipeline_v9_flat_clocked_ghdl_spec.spl`; bootstrap-seed output, source/topology assertions, and any unadmitted GHDL run are development evidence only—not a qualification PASS.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 5 | 5 | 0 | 0 |

## Scenario flow

1. Elaborate the exact RV32IM/RV64IM Zicsr profiles and verify the ordered 21 direct children.
2. Verify every base M row, RV64 word-M row, tag-two dispatch, accept, held completion, and consume wiring.
3. Verify class-six/tag-three CSR routing and the XLEN-aware lookup/read/commit service ABI.
4. Compile the same RV32 combined product twice and compare route, graph, receipt, and emitted VHDL.
5. Reject IM-only, Zmmul-only, and standalone-Zicsr profiles.

Requirements: `REQ-G2-012`, `REQ-G2-013`, `REQ-G2-016`, `REQ-G2-017`, and
`NFR-G2-003`. REQ-G2-017's direct effect-owner and cycle evidence is maintained
by `riscv_gen2_fence_owner_spec` and `riscv_scalar_fence_product_cycle_ghdl_spec`;
this V9 scenario does not claim that those standalone tests qualify the full V9
pipeline.

Runnable source: `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v9_im_zicsr_spec.spl`.
When an admitted self-hosted runtime is available, generate this manual with:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v9_im_zicsr_spec.spl --output doc/06_spec --no-index
```

Final qualification additionally requires an admitted V9 full-pipeline clocked GHDL run and required generated-RTL formal/RVFI evidence; neither is substituted by this structural trace.
