# RISC-V Gen2 V7 flattened IM runtime-M pipeline

Status: development structural evidence. V7 is exactly RV32IM/RV64IM, with one
flat tag-two runtime-M owner for MUL, high multiply, DIV, and REM families. It
does not include Zmmul-only or CSR profiles.

Qualification is **BLOCKED**: no admitted pure-Simple self-hosted runtime is
available for this exact scenario. `ghdl` is callable, but no admitted V7
execution result is retained. The existing clocked scenario is provider-only:
`test/02_integration/compiler/riscv_scalar_runtime_m_provider_ghdl_spec.spl`.
It is not a full-pipeline bench and lacks RV32 multiply vectors. Bootstrap-seed
output and source/topology assertions are development evidence, not a
qualification PASS.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 5 | 5 | 0 | 0 |

## Scenario flow

1. Elaborate RV32IM and RV64IM pipelines; verify one flat tag-two owner.
2. Verify all eight base M rows, plus RV64 `MULW`, `DIVW`, `DIVUW`, `REMW`, and
   `REMUW` rows, originate in the exact IM plans.
3. Verify pending-to-owner request, accept, held completion, consume, and
   protocol-fault wiring.
4. Compile the same RV32IM product twice and compare route, graph, receipt,
   and emitted VHDL.
5. Reject Zmmul-only and CSR profiles to preserve the IM-only boundary.

Requirements: `REQ-G2-012`, `REQ-G2-013`, and `NFR-G2-003`.

Runnable source: `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v7_im_spec.spl`.
When an admitted runtime is available, generate this manual with:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v7_im_spec.spl --output doc/06_spec --no-index
```

Final qualification additionally requires an admitted run of the provider
clocked scenario, a new admitted full-pipeline clocked GHDL scenario covering
all RV32/RV64 M rows, and generated-RTL formal/RVFI readiness evidence.
