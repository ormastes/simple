# RV32 NVMe NAND Read-Level Agent Tasks

| Lane | Owner | Write scope | Output |
|---|---|---|---|
| Research/local gap | Bernoulli sidecar | N/A | reviewed gap report |
| FPGA/JTAG audit | Curie sidecar | N/A | reviewed runner report |
| AXI topology audit | Arendt sidecar | N/A | full-AXI vs BRAM path report |
| `.nandram` access audit | McClintock sidecar | N/A | load/store and test trace report |
| Merge and implementation | Codex | feature files | one coherent change |
| Final review | highest-capability Codex | N/A | verify verdict |

Interface names are fixed by the design: `rv32_nand_*` pure helpers,
`_nand_ram_*` RV32 storage helpers, nine ordered `NAND ... PASS` markers, and
the final `ALL RV32 NVME FW CHECKS PASS` marker.
